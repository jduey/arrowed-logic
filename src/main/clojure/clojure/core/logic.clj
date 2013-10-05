;;; 
(ns clojure.core.logic
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols])
  (:require [clojure.set :as set]
            [clojure.string :as string]
            [monads.core :as m]
            [monads.macros :as mm]
            [arrows :as a]
            [arrows.vis :as v])
  (:import [java.io Writer]
           [java.util UUID]
           monads.core.state-transformer
           [clojure.core.logic.protocols
            IBindable ITreeTerm IVar ITreeConstraint INonStorable]))

(def ^{:dynamic true} *locals*)

(def fk (Exception.))

;; =============================================================================
;; Utilities

(defn assoc-meta [x k v]
  (with-meta x (assoc (meta x) k v)))

(defn dissoc-meta [x k]
  (with-meta x (dissoc (meta x) k)))

(defn assoc-dom [x k v]
  (assoc x :doms (assoc (:doms x) k v)))

(defn dissoc-dom [x k]
  (assoc x :doms (dissoc (:doms x) k)))

(defn record? [x]
  (instance? clojure.lang.IRecord x))

;; =============================================================================
;; Pair

(deftype Pair [lhs rhs]
  clojure.lang.ILookup
  (valAt [this k]
    (.valAt this k nil))
  (valAt [this k not-found]
    (case k
      :lhs lhs
      :rhs rhs
      not-found))

  clojure.lang.Counted
  (count [_] 2)

  clojure.lang.Indexed
  (nth [_ i] (case i
               0 lhs
               1 rhs
               (throw (IndexOutOfBoundsException.))))
  (nth [_ i not-found] (case i
                         0 lhs
                         1 rhs
                         not-found))

  java.util.Map$Entry
  (getKey [_] lhs)
  (getValue [_] rhs)

  Object
  (toString [_]
    (str "(" lhs " . " rhs ")"))

  (equals [_ o]
    (if (instance? Pair o)
      (and (= lhs (:lhs o))
           (= rhs (:rhs o)))
      false)))

(defn- pair [lhs rhs]
  (Pair. lhs rhs))

(defmethod print-method Pair [x ^Writer writer]
  (.write writer (str "(" (:lhs x) " . " (:rhs x) ")")))

;; =============================================================================
;; Constraint Store

(declare lvar? bindable? add-var)

(defn var-rands [a c]
  (->> (-rands c)
       (map #(root-var a %))
       (filter lvar?)
       (into [])))

(defn unbound-rands [a c]
  (->> (var-rands a c)
       (filter #(lvar? (root-val a %)))))

;; ConstraintStore
;; -----
;; km  - mapping logic vars to constraints ids
;; cm  - mapping constraint ids to to actual constraints
;; cid - the current constraint id, an integer, incremented
;;       everytime we add a constraint to the store
;; running - set of running constraint ids

(deftype ConstraintStore [km cm cid running]
  clojure.lang.ILookup
  (valAt [this k]
    (.valAt this k nil))
  (valAt [this k not-found]
    (case k
      :km km
      :cm cm
      :cid cid
      :running running
      not-found))

  IConstraintStore
  (addc [this a c]
    (let [vars (var-rands a c)
          c (with-id c cid)
          cs (reduce (fn [cs v] (add-var cs v c)) this vars)]
      (ConstraintStore. (:km cs) (:cm cs) (inc cid) running)))

  (updatec [this a c]
    (let [oc (cm (id c))
          nkm (if (instance? clojure.core.logic.protocols.IEntailedVar c)
                (reduce (fn [km x]
                          (if (-entailed-var? c x)
                            (dissoc km x)
                            km))
                        km (var-rands a oc))
                km)]
      (ConstraintStore. nkm (assoc cm (id c) c) cid running)))

  (remc [this a c]
    (let [vs (var-rands a c)
          ocid (id c)
          nkm (reduce (fn [km v]
                        (let [vcs (disj (get km v) ocid)]
                          (if (empty? vcs)
                            (dissoc km v)
                            (assoc km v vcs))))
                      km vs)
          ncm (dissoc cm ocid)]
      (ConstraintStore. nkm ncm cid running)))

  (runc [this c state]
    (if state
      (ConstraintStore. km cm cid (conj running (id c)))
      (ConstraintStore. km cm cid (disj running (id c)))))

  (constraints-for [this a x ws]
    (when-let [ids (get km (root-var a x))]
      (filter #((-watched-stores %) ws) (map cm (remove running ids)))))

  (migrate [this x root]
    (let [xcs    (km x)
          rootcs (km root #{})
          nkm    (assoc (dissoc km x) root (into rootcs xcs))]
      (ConstraintStore. nkm cm cid running)))

  clojure.lang.Counted
  (count [this]
    (count cm)))

(defn add-var [cs x c]
  (when-not (lvar? x)
    (throw (Error. (str "constraint store assoc expected logic var key: " x))))
  (let [cm (:cm cs)
        km (:km cs)
        cid (:cid cs)
        nkm (update-in km [x] (fnil (fn [s] (conj s cid)) #{}))
        ncm (assoc cm cid c)]
    (ConstraintStore. nkm ncm cid (:running cs))))

(defn make-cs []
  (ConstraintStore. {} {} 0 #{}))

;; =============================================================================
;; SubstValue
;; v - the actual ground value of the var
;; doms - the constraint domains assigned to the var
;; eset - set of other vars this var is entangled with

(defrecord SubstValue [v doms eset]
  Object
  (toString [_]
    (str v)))

(defn subst-val? [x]
  (instance? SubstValue x))

(defn subst-val
  ([x] (SubstValue. x nil nil))
  ([x doms] (SubstValue. x doms nil))
  ([x doms _meta] (with-meta (SubstValue. x doms nil) _meta))
  ([x doms eset _meta] (with-meta (SubstValue. x doms eset) _meta)))

;; =============================================================================
;; Substitutions

(declare empty-s choice lvar lvar? pair lcons logic-m run-constraints*)

(defn occurs-check [s u v]
  (let [v (walk s v)]
    (occurs-check-term v u s)))

(defn ext [s u v]
  (if (and (:oc s) (occurs-check s u (if (subst-val? v) (:v v) v)))
    nil
    (ext-no-check s u v)))

(declare tree-term?)

(defn walk* [s v]
  (let [v (walk s v)]
    (walk-term v
               (fn [x]
                 (let [x (walk s x)]
                   (if (tree-term? x)
                     (walk* s x)
                     x))))))

(defn unify [s u v]
  (if (identical? u v)
    s
    (let [u  (walk s u)
          v  (walk s v)]
      ;; TODO: we can't use an identical? check here at the moment
      ;; because we add metadata on vars in walk - David
      (if (and (lvar? u) (= u v))
        s
        (if (and (not (lvar? u)) (lvar? v))
          (unify-terms v u s)
          (unify-terms u v s))))))

(def unbound-names
  (let [r (range 100)]
    (zipmap r (map (comp symbol str) (repeat "_") r))))

(defn reify-lvar-name [s]
  (let [c (count s)]
    (if (< c 100)
      (unbound-names c)
      (symbol (str "_" (count s))))))

(defn -reify* [s v]
  (let [v (walk s v)]
    (reify-term v s)))

(defn -reify
  ([s v]
     (let [v (walk* s v)]
       (walk* (-reify* (with-meta empty-s (meta s)) v) v)))
  ([s v r]
     (let [v (walk* s v)]
       (walk* (-reify* r v) v))))

(defn build [s u]
  (build-term u s))

(declare empty-s make-s)

;; Substitutions
;; -----
;; s   - persistent hashmap to store logic var bindings
;; vs  - changed var set
;; ts  - atom containing a hashmap of
;;       tabled goals -> atoms of sets containing cached answers
;; cs  - constraint store
;; cq  - for the constraint queue
;; cqs - constraint ids in the queue
;; oc  - occurs check

(deftype Substitutions [s vs ts cs cq cqs oc _meta]
  Object
  (equals [this o]
    (or (identical? this o)
        (and (.. this getClass (isInstance o))
             (= s (:s o)))))
  ;; TODO: prn doesn't work anymore on empty-s, why not?
  (toString [_] (str s))

  clojure.lang.Counted
  (count [this] (count s))

  clojure.lang.IObj
  (meta [this] _meta)
  (withMeta [this new-meta]
    (Substitutions. s vs ts cs cq cqs oc new-meta))

  clojure.lang.ILookup
  (valAt [this k]
    (.valAt this k nil))
  (valAt [this k not-found]
    (case k
      :s   s
      :vs  vs
      :ts  ts
      :cs  cs
      :cq  cq
      :cqs cqs
      :oc  oc
      not-found))

  clojure.lang.IPersistentCollection
  (cons [this [k v]]
    (if (lvar? k)
      (assoc this k v)
      (throw (Exception. (str "key must be a logic var")))))
  (empty [this] empty-s)
  (equiv [this o]
    (.equals this o))

  clojure.lang.Associative
  (containsKey [this k]
    (contains? #{:s :vs :cs :cq :cqs :oc} k))
  (entryAt [this k]
    (case k
      :s   [:s s]
      :vs  [:vs vs]
      :ts  [:ts ts]
      :cs  [:cs cs]
      :cq  [:cq cq]
      :cqs [:cqs cqs]
      :oc  [:oc cqs]
      nil))
  (assoc [this k v]
    (case k
      :s   (Substitutions. v vs ts cs cq cqs oc _meta)
      :vs  (Substitutions. s  v ts cs cq cqs oc _meta)
      :ts  (Substitutions. s vs  v cs cq cqs oc _meta)
      :cs  (Substitutions. s vs ts  v cq cqs oc _meta)
      :cq  (Substitutions. s vs ts cs  v cqs oc _meta)
      :cqs (Substitutions. s vs ts cs cq   v oc _meta)
      :oc  (Substitutions. s vs ts cs cq cqs  v _meta)
      (throw (Exception. (str "Substitutions has no field for key" k)))))

  ISubstitutions
  (ext-no-check [this u v]
    (let [u (if-not (lvar? v)
              (assoc-meta u ::root true)
              u)]
      (Substitutions. (assoc s u v) (if vs (conj vs u)) ts cs cq cqs oc _meta)))

  (walk [this v]
    (if (bindable? v)
      (loop [lv v [v vp :as me] (find s v)]
        (cond
         (nil? me) lv

         (not (bindable? vp))
         (if (subst-val? vp)
           (let [sv (:v vp)]
             (if (= sv ::unbound)
               (with-meta v (assoc (meta vp) ::unbound true))
               sv))
           vp)

         :else (recur vp (find s vp))))
      v))

  ISubstitutionsCLP
  (root-val [this v]
    (if (lvar? v)
      (loop [lv v [v vp :as me] (find s v)]
        (cond
         (nil? me) lv
         (not (lvar? vp)) vp
         :else (recur vp (find s vp))))
      v))

  (root-var [this v]
    (if (lvar? v)
      (if (-> v meta ::root)
        v
        (loop [lv v [v vp :as me] (find s v)]
          (cond
           (nil? me) lv

           (not (lvar? vp))
           (if (subst-val? vp)
             (with-meta v (meta vp))
             v)

           :else (recur vp (find s vp)))))
      v))

  (ext-run-cs [this x v]
    (let [x  (root-var this x)
          xs (if (lvar? v)
               [x (root-var this v)]
               [x])
          s  (if oc
               (ext this x v)
               (ext-no-check this x v))]
      (when s
        ((run-constraints* xs cs ::subst) s))))

  (queue [this c]
    (let [id (id c)]
      (if-not (cqs id)
        (-> this
            (assoc :cq (conj (or cq []) c))
            (assoc :cqs (conj cqs id)))
        this)))

  (update-var [this x v]
    (assoc this :s (assoc (:s this) x v)))

  IBind
  (bind [this g]
    (g this))
  IMPlus
  (mplus [this f]
    (choice this f))
  ITake
  (take* [this] this))

(defn add-attr [s x attr attrv]
  (let [x (root-var s x)
        v (root-val s x)]
    (if (subst-val? v)
      (update-var s x (assoc-meta v attr attrv))
      (let [v (if (lvar? v) ::unbound v)]
        (ext-no-check s x (with-meta (subst-val v) {attr attrv}))))))

(defn rem-attr [s x attr]
  (let [x (root-var s x)
        v (root-val s x)]
    (if (subst-val? v)
      (let [new-meta (dissoc (meta v) attr)]
        (if (and (zero? (count new-meta)) (not= (:v v) ::unbound))
          (update-var s x (:v v))
          (update-var s x (with-meta v new-meta))))
      s)))

(defn get-attr [s x attr]
  (let [v (root-val s x)]
    (if (subst-val? v)
      (-> v meta attr))))

(defn sync-eset [s v seenset f]
  (if (not= seenset ::no-prop)
    (reduce
     (fn [s y]
       (let [y (root-var s y)]
         (if-not (contains? seenset y)
           (f s y)
           s)))
     s
     (:eset v))
    s))

(defn add-dom
  ([s x dom domv]
     (let [x (root-var s x)]
       (add-dom s x dom domv nil)))
  ([s x dom domv seenset]
     (let [v (root-val s x)
           s (if (subst-val? v)
               (update-var s x (assoc-dom v dom domv))
               (let [v (if (lvar? v) ::unbound v)]
                 (ext-no-check s x (subst-val v {dom domv}))))]
       (sync-eset s v seenset
                  (fn [s y] (add-dom s y dom domv (conj (or seenset #{}) x)))))))

(defn update-dom
  ([s x dom f]
     (let [x (root-var s x)]
       (update-dom s x dom f nil)))
  ([s x dom f seenset]
     (let [v (root-val s x)
           v (if (lvar? v)
               (subst-val ::unbound)
               v)
           doms (:doms v)
           s (update-var s x (assoc-dom v dom (f (get doms dom))))]
       (sync-eset s v seenset
                  (fn [s y] (update-dom s y dom f (conj (or seenset #{}) x)))))))

(defn rem-dom
  ([s x dom]
     (let [x (root-var s x)]
       (rem-dom s x dom nil)))
  ([s x dom seenset]
     (let [v (root-val s x)
           s (if (subst-val? v)
               (let [new-doms (dissoc (:doms v) dom)]
                 (if (and (zero? (count new-doms)) (not= (:v v) ::unbound))
                   (update-var s x (:v v))
                   (update-var s x (assoc v :doms new-doms))))
               s)]
       (sync-eset s v seenset
                  (fn [s y] (rem-dom s y dom (conj (or seenset #{}) x)))))))

;; NOTE: I don't think we need to bother returning ::not-dom or some other
;; not found value. Assume the case where the var is bound to nil in
;; the substitution where the var has a domain. That the var is member
;; will be verified by domc or something similar. The case where the var
;; is nil and has no domain is trivial.

(defn get-dom [s x dom]
  (let [v (root-val s x)]
    (cond
     (subst-val? v) (let [v' (:v v)]
                      (if (not= v' ::unbound)
                        v'
                        (-> v :doms dom)))
     (not (lvar? v)) v)))

(defn- make-s
  ([] (make-s {}))
  ([m] (make-s m (make-cs)))
  ([m cs] (Substitutions. m nil nil cs nil #{} true nil)))

(defn tabled-s
  ([] (tabled-s false))
  ([oc] (tabled-s oc nil))
  ([oc meta]
     (-> (with-meta (make-s) meta)
         (assoc :oc oc)
         (assoc :ts (atom {})))))

(def empty-s (make-s))
(def empty-f (fn []))

(defn subst? [x]
  (instance? Substitutions x))

(defn to-s [v]
  (let [s (reduce (fn [m [k v]] (assoc m k v)) {} v)]
    (make-s s (make-cs))))

(defn annotate [k v]
  (fn [a]
    (vary-meta a assoc k v)))

;; NOTE: this may result in some redundant computations
;; in particular complex nominal logic programs that involve
;; FD and other similar constraint domains.
;; In nominal programs like quine generation we actually see
;; exponential behavior, so we'll probably want to revisit
;; this code at some point - David

(defn merge-doms [s x doms]
  (let [xdoms (:doms (root-val s x))]
    (loop [doms (seq doms) s s]
      (if doms
        (let [[dom domv] (first doms)]
          (let [xdomv (get xdoms dom ::not-found)
                ndomv (if (= xdomv ::not-found)
                        domv
                        (-merge-doms domv xdomv))]
            (when ndomv
              (recur (next doms)
                     (add-dom s x dom ndomv #{})))))
        s))))

(defn update-eset [s doms eset]
  (loop [eset (seq eset) s s]
    (if eset
      (when-let [s (merge-doms s (root-var s (first eset)) doms)]
        (recur (next eset) s))
      s)))

(defn merge-with-root [s x root]
  (let [xv    (root-val s x)
        rootv (root-val s root)
        eset  (set/union (:eset rootv) (:eset xv))
        doms (loop [xd (seq (:doms xv)) rd (:doms rootv) r {}]
               (if xd
                 (let [[xk xv] (first xd)]
                   (if-let [[_ rv] (find rd xk)]
                     (let [nd (-merge-doms xv rv)]
                       (when nd
                         (recur (next xd)
                                (dissoc rd xk) (assoc r xk nd))))
                     (recur (next xd) rd (assoc r xk xv))))
                 (merge r rd)))
        nv (when doms
             (subst-val (:v rootv) doms eset
                        (merge (meta xv) (meta rootv))))]
    (when nv
      (-> s
          (ext-no-check root nv)
          (update-eset doms eset)))))

;; =============================================================================
;; Entanglement

(defn to-subst-val [v]
  (if (subst-val? v)
    v
    (subst-val ::unbound)))

(defn entangle [s x y]
  (let [x  (root-var s x)
        y  (root-var s y)
        xv (to-subst-val (root-val s x))
        yv (to-subst-val (root-val s y))]
    (-> s
        (update-var x (assoc xv :eset (conj (or (:eset xv) #{}) y)))
        (update-var y (assoc yv :eset (conj (or (:eset yv) #{}) x))))))

;; =============================================================================
;; Logic Variables

(deftype LVar [name oname hash meta]
  IVar
  clojure.lang.ILookup
  (valAt [this k]
    (.valAt this k nil))
  (valAt [this k not-found]
    (case k
      :name name
      :oname oname
      not-found))

  clojure.lang.IObj
  (meta [this]
    meta)
  (withMeta [this new-meta]
    (LVar. name oname hash new-meta))

  Object
  (toString [_] (str "<lvar:" name ">"))

  (equals [this o]
    (and (instance? IVar o)
         (identical? name (:name o))))

  (hashCode [_] hash)

  IUnifyTerms
  (unify-terms [u v s]
    (cond
     (lvar? v)
     (let [repoint (cond
                    (-> u clojure.core/meta ::unbound) [u v]
                    (-> v clojure.core/meta ::unbound) [v u]
                    :else nil)]
       (if repoint
         (let [[root other] repoint
               s (assoc s :cs (migrate (:cs s) other root))
               s (if (-> other clojure.core/meta ::unbound)
                   (merge-with-root s other root)
                   s)]
           (when s
             (ext-no-check s other root)))
         (ext-no-check s u v)))

     (non-storable? v)
     (throw (Exception. (str v " is non-storable")))

     (not= v ::not-found)
     (if (tree-term? v)
       (ext s u v)
       (if (-> u clojure.core/meta ::unbound)
         (ext-no-check s u (assoc (root-val s u) :v v))
         (ext-no-check s u v)))

     :else nil))

  IReifyTerm
  (reify-term [v s]
    (let [rf (-> s clojure.core/meta :reify-vars)]
      (if (fn? rf)
        (rf v s)
        (if rf
          (ext s v (reify-lvar-name s))
          (ext s v (:oname v))))))

  IWalkTerm
  (walk-term [v f] (f v))

  IOccursCheckTerm
  (occurs-check-term [v x s] (= (walk s v) x))

  IBuildTerm
  (build-term [u s]
    (let [m (:s s)
          cs (:cs s)
          lv (lvar 'ignore) ]
      (if (contains? m u)
        s
        (make-s (assoc m u lv) cs)))))

(defn lvar
  ([]
     (let [name (str (. clojure.lang.RT (nextID)))]
       (LVar. name nil (.hashCode name) nil)))
  ([name]
     (lvar name true))
  ([name gensym]
     (let [oname name
           name (if gensym
                  (str name "__" (. clojure.lang.RT (nextID)))
                  (str name))]
       (LVar. name oname (.hashCode name) nil))))

(defmethod print-method LVar [x ^Writer writer]
  (.write writer (str "<lvar:" (:name x) ">")))

(defn lvar? [x]
  (instance? IVar x))

(defn lvars [n]
  (repeatedly n lvar))

(defn bindable? [x]
  (or (lvar? x)
      (instance? IBindable x)))

;; =============================================================================
;; LCons

(declare lcons?)

(defmacro umi
  [& args]
  (if (resolve 'unchecked-multiply-int)
    `(unchecked-multiply-int ~@args)
    `(unchecked-multiply ~@args)))

(defmacro uai
  [& args]
  (if (resolve 'unchecked-add-int)
    `(unchecked-add-int ~@args)
    `(unchecked-add ~@args)))

;; TODO: clean up the printing code

(deftype LCons [a d ^{:unsynchronized-mutable true :tag int} cache meta]
  ITreeTerm
  clojure.lang.IObj
  (meta [this]
    meta)
  (withMeta [this new-meta]
    (LCons. a d cache new-meta))

  LConsSeq
  (lfirst [_] a)
  (lnext [_] d)

  LConsPrint
  (toShortString [this]
    (cond
     (.. this getClass (isInstance d)) (str a " " (toShortString d))
     :else (str a " . " d )))

  Object
  (toString [this] (cond
                    (.. this getClass (isInstance d))
                    (str "(" a " " (toShortString d) ")")
                    :else (str "(" a " . " d ")")))

  (equals [this o]
    (or (identical? this o)
        (and (.. this getClass (isInstance o))
             (loop [me this
                    you o]
               (cond
                (nil? me) (nil? you)
                (lvar? me) true
                (lvar? you) true
                (and (lcons? me) (lcons? you))
                (let [mef  (lfirst me)
                      youf (lfirst you)]
                  (and (or (= mef youf)
                           (lvar? mef)
                           (lvar? youf))
                       (recur (lnext me) (lnext you))))
                :else (= me you))))))

  (hashCode [this]
    (if (= cache -1)
      (do
        (set! cache (uai (umi (int 31) (clojure.lang.Util/hash d))
                         (clojure.lang.Util/hash a)))
        cache)
      cache))

  IUnifyTerms
  (unify-terms [u v s]
    (cond
     (sequential? v)
     (loop [u u v v s s]
       (if (seq v)
         (if (lcons? u)
           (if-let [s (unify s (lfirst u) (first v))]
             (recur (lnext u) (next v) s)
             nil)
           (unify s u v))
         (if (lvar? u)
           (if-let [s (unify s u '())]
             s
             (unify s u nil))
           nil)))

     (lcons? v)
     (loop [u u v v s s]
       (if (lvar? u)
         (unify s u v)
         (cond
          (lvar? v) (unify s v u)
          (and (lcons? u) (lcons? v))
          (if-let [s (unify s (lfirst u) (lfirst v))]
            (recur (lnext u) (lnext v) s)
            nil)
          :else (unify s u v))))

     :else nil))

  IReifyTerm
  (reify-term [v s]
    (loop [v v s s]
      (if (lcons? v)
        (recur (lnext v) (-reify* s (lfirst v)))
        (-reify* s v))))

  ;; TODO: no way to make this non-stack consuming w/o a lot more thinking
  ;; we could use continuation passing style and trampoline
  IWalkTerm
  (walk-term [v f]
    (lcons (f (lfirst v))
           (f (lnext v))))

  IOccursCheckTerm
  (occurs-check-term [v x s]
    (loop [v v x x s s]
      (if (lcons? v)
        (or (occurs-check s x (lfirst v))
            (recur (lnext v) x s))
        (occurs-check s x v))))

  IBuildTerm
  (build-term [u s]
    (loop [u u s s]
      (if (lcons? u)
        (recur (lnext u) (build s (lfirst u)))
        (build s u)))))

(defmethod print-method LCons [x ^Writer writer]
  (.write writer (str x)))

(defn lcons
  "Constructs a sequence a with an improper tail d if d is a logic variable."
  [a d]
  (if (or (coll? d) (nil? d))
    (cons a (seq d))
    (LCons. a d -1 nil)))

(defn lcons? [x]
  (instance? LCons x))

(defmacro llist
  "Constructs a sequence from 2 or more arguments, with the last argument as the
   tail. The tail is improper if the last argument is a logic variable."
  ([f s] `(lcons ~f ~s))
  ([f s & rest] `(lcons ~f (llist ~s ~@rest))))

(defn tree-term? [x]
  (or (coll? x)
      (instance? ITreeTerm x)))

;; =============================================================================
;; Unification

;; TODO : a lot of cascading ifs need to be converted to cond

(defn unify-with-sequential* [u v s]
  (cond
   (sequential? v)
   (if (and (counted? u) (counted? v)
            (not= (count u) (count v)))
     nil
     (loop [u u v v s s]
       (if (seq u)
         (if (seq v)
           (if-let [s (unify s (first u) (first v))]
             (recur (next u) (next v) s)
             nil)
           nil)
         (if (seq v) nil s))))

   (lcons? v) (unify-terms v u s)
   :else nil))

(defn unify-with-map* [u v s]
  (when (= (count u) (count v))
    (loop [ks (keys u) s s]
      (if (seq ks)
        (let [kf (first ks)
              vf (get v kf ::not-found)]
          (when-not (= vf ::not-found)
            (if-let [s (unify s (get u kf) vf)]
              (recur (next ks) s)
              nil)))
        s))))

(extend-protocol IUnifyTerms
  nil
  (unify-terms [u v s]
    (if (nil? v) s nil))

  Object
  (unify-terms [u v s]
    (if (= u v)
      s
      nil))

  clojure.lang.Sequential
  (unify-terms [u v s]
    (unify-with-sequential* u v s))

  clojure.lang.IPersistentMap
  (unify-terms [u v s]
    (cond
     (instance? clojure.core.logic.protocols.IUnifyWithRecord v)
     (unify-with-record v u s)

     (map? v)
     (unify-with-map* u v s)

     :else nil)))

;; =============================================================================
;; Reification

(extend-protocol IReifyTerm
  nil
  (reify-term [v s] s)

  Object
  (reify-term [v s] s)

  clojure.lang.IPersistentCollection
  (reify-term [v s]
    (loop [v v s s]
      (if (seq v)
        (recur (next v) (-reify* s (first v)))
        s))))

;; =============================================================================
;; Walk Term

(defn walk-record-term [v f]
  (with-meta
    (loop [v v r (-uninitialized v)]
      (if (seq v)
        (let [[vfk vfv] (first v)]
          (recur (next v) (assoc r (walk-term (f vfk) f)
                                 (walk-term (f vfv) f))))
        r))
    (meta v)))

(extend-protocol IWalkTerm
  nil
  (walk-term [v f] (f nil))

  Object
  (walk-term [v f] (f v))

  clojure.lang.ISeq
  (walk-term [v f]
    (with-meta
      (doall (map #(walk-term (f %) f) v))
      (meta v)))

  clojure.lang.IPersistentVector
  (walk-term [v f]
    (with-meta
      (loop [v v r (transient [])]
        (if (seq v)
          (recur (next v) (conj! r (walk-term (f (first v)) f)))
          (persistent! r)))
      (meta v)))

  clojure.lang.IPersistentMap
  (walk-term [v f]
    (if (record? v)
      (walk-record-term v f)
      (with-meta
        (loop [v v r (transient {})]
          (if (seq v)
            (let [[vfk vfv] (first v)]
              (recur (next v) (assoc! r (walk-term (f vfk) f)
                                      (walk-term (f vfv) f))))
            (persistent! r)))
        (meta v))))

  clojure.lang.IRecord
  (walk-term [v f]
    (walk-record-term v f)))

;; =============================================================================
;; Occurs Check Term

(extend-protocol IOccursCheckTerm
  nil
  (occurs-check-term [v x s] false)

  Object
  (occurs-check-term [v x s] false)

  clojure.lang.IPersistentCollection
  (occurs-check-term [v x s]
    (loop [v v x x s s]
      (if (seq v)
        (or (occurs-check s x (first v))
            (recur (next v) x s))
        false))))

;; =============================================================================
;; Build Term

(extend-protocol IBuildTerm
  nil
  (build-term [u s] s)

  Object
  (build-term [u s] s)

  clojure.lang.IPersistentCollection
  (build-term [u s]
    (reduce build s u)))

;; =============================================================================
;; Goals and Goal Constructors

(defn composeg
  ([] identity)
  ([g0 g1]
     (fn [a]
       (let [a (g0 a)]
         (and a (g1 a))))))

(defmacro composeg*
  ([g0] g0)
  ([g0 & gs]
     `(composeg
       ~g0
       (composeg* ~@gs))))

(defmacro bind*
  ([a g] `(bind ~a ~g))
  ([a g & g-rest]
     `(bind* (bind ~a ~g) ~@g-rest)))

(defmacro mplus*
  ([e] e)
  ([e & e-rest]
     `(mplus ~e (fn [] (mplus* ~@e-rest)))))

(defmacro -inc [& rest]
  `(fn -inc [] ~@rest))

(extend-type Object
  ITake
  (take* [this] this))

(deftype Choice [a f]
  clojure.lang.ILookup
  (valAt [this k]
    (.valAt this k nil))
  (valAt [this k not-found]
    (case k
      :a a
      not-found))
  IBind
  (bind [this g]
    (mplus (g a) (fn [] (bind f g))))
  IMPlus
  (mplus [this fp]
    (Choice. a (fn [] (mplus (fp) f))))
  ITake
  (take* [this]
    (lazy-seq (cons a (lazy-seq (take* f))))))

(defn choice [a f]
  (Choice. a f))

;; -----------------------------------------------------------------------------
;; MZero

(extend-type nil
  IBind
  (bind [_ g] nil)
  IMPlus
  (mplus [_ f] (f))
  ITake
  (take* [_] '()))

;; -----------------------------------------------------------------------------
;; Unit

(extend-type Object
  IMPlus
  (mplus [this f]
    (Choice. this f)))

;; -----------------------------------------------------------------------------
;; Inc

(extend-type clojure.lang.Fn
  IBind
  (bind [this g]
    (-inc (bind (this) g)))
  IMPlus
  (mplus [this f]
    (-inc (mplus (f) this)))
  ITake
  (take* [this] (lazy-seq (take* (this)))))

;; =============================================================================
;; tree-building monad

(def tree-m (m/state-t m/cont))
(defn tree-cc [f]
  (state-transformer. m/cont nil
                      (tree-m nil)
                      (fn [_]
                        (fn [m]
                          (fn [c]
                            (f m c))))
                      nil))

(defn build-tree
  ([tree-fn] (build-tree tree-fn #{}))
  ([tree-fn m] (build-tree tree-fn m identity))
  ([tree-fn m c] ((tree-fn m) c)))

;; =============================================================================
;; drawing the search tree

(defn make-graph
  ([p] (make-graph p {} {} (fn [[g m]]
                            [(v/append-dg g {:id (v/genkey)}) m])))
  ([p g m c]
     (build-tree ((get (meta p) :tree) g) m c)))

(defn proc-to-dot [p]
  (let [dg (first (make-graph p))]
    (->> dg
         (v/dg-to-dot)
         :body
         (str (format "subgraph start {\nstart [label = \"start\"];}\nstart -> %s;\n"
                      (name (v/entry-id dg)))))))

;; =============================================================================
;; Syntax

(def logic-m vector)
(def logic-zero (m/zero (logic-m nil)))

(defn run-logic [goal]
  (goal empty-s))

(defmacro run* [[x] & goals]
  ;; TODO: thread this
  `(let [~x (clojure.core.logic/lvar '~x)
         p# (first (clojure.core.logic/build-tree (clojure.core.logic/all ~@goals)))]
     (map #(-reify % ~x) (clojure.core.logic/run-logic p#))))

(defmacro run [n x & goals]
  `(take ~n (clojure.core.logic/run* ~x ~@goals)))

(defn- add-branch [g branch-dg]
  (-> g
      (assoc (:id branch-dg) branch-dg)
      (update-in [(:entry g) :next] conj
                 {:to (v/entry-id branch-dg)})))

(defn- par-to-tree [ps]
  (if (= 1 (count ps))
    (get (meta (first ps)) :tree)
    (fn [g]
      (tree-cc (fn [m c]
                 (let [entry (v/genkey)
                       bg (reduce add-branch
                                  {:id (v/genkey)
                                   :entry entry
                                   entry {:id entry :next []}}
                                  (map #(first (make-graph % {} m c)) ps))]
                   [(v/append-dg g bg)
                    m]))))))

(def remove-fails (atom true))
(def prune-empty (atom true))
(def show-unify (atom true))

(deftype logic-arr [fun meta-data]
  clojure.lang.IDeref
  (deref [_]
    [fun meta-data])

  clojure.lang.IMeta
  (meta [_]
    meta-data)

  clojure.lang.IFn
  (invoke [_ x]
    (fun x))

  a/Arrow
  (arrow-arr [_ f]
    (logic-arr. (comp logic-m f)
                {:op :arrow-arr
                 :tree tree-m
                 :label ""}))

  (arrow-seq [p ps]
    (if (empty? ps)
      p
      (let [ps (cons p ps)
            ps (sort-by meta
                        (comparator (fn [p-meta _]
                                      (not (contains? p-meta :self-recursive))))
                        ps)
            self-recursive (apply set/union (map #(get (meta %) :self-recursive) ps))]
        (logic-arr. (m/chain ps)
                    {:op :arrow-seq
                     :tree (->> ps
                                (map #(get (meta %) :tree))
                                m/chain)
                     :self-recursive self-recursive
                     :results (apply * (map #(get (meta %) :results 1) ps))
                     :args ps}))))

  ;; we don't need this for the logic arrow
  (arrow-nth [p n]
    (logic-arr. (fn [ss]
                  nil)
                {}))

  a/ArrowPar
  (arrow-par [p ps]
    (let [ps (cons p ps)
          ps (if @remove-fails
               (remove #(= 0 (v/get-attr % :results)) ps)
               ps)
          self-recursive (apply set/union (map #(get (meta %) :self-recursive) ps))]
      (cond
       (empty? ps)
       (logic-arr. (constantly logic-zero)
                   {:op :arrow-arr
                    :fail true
                    :results 0
                    :tree (fn [g]
                            (tree-cc
                             (fn [m c]
                               [(v/append-dg g {:id (v/genkey)
                                                :label "fail"})
                                m])))})

       (= (count ps) 1)
       (first ps)

       :else
       (logic-arr. (fn [ss]
                     (logic-m (map #(%1 %2) ps ss)))
                   {:op :arrow-par
                    :self-recursive self-recursive
                    :results (reduce #(+ %1 %2) (map #(get (meta %) :results 1) ps))
                    :tree (par-to-tree ps)}))))

  arrows.vis/ArrowVis
  (get-attr [p attr-key]
    (get (meta p) attr-key))
  (set-attr* [p kv-pairs]
    (let [[f m] (deref p)]
      (logic-arr. f (apply assoc m kv-pairs))))
  (op [p]
    (:op (meta p)))
  (args [p]
    (:args (meta p)))
  (label [p lbl]
    (let [[f m] (deref p)]
      (logic-arr. f (assoc m :label lbl)))))

(defn arr [f]
  (logic-arr. (comp logic-m f)
              {:op :arrow-arr
               :tree tree-m
               :label ""}))

(def fail-p (logic-arr. (constantly logic-zero)
                        {:op :arrow-arr
                         :fail true
                         :results 0
                         :tree (fn [g]
                                 (tree-cc
                                  (fn [m c]
                                    [(v/append-dg g {:id (v/genkey)
                                                     :label "fail"})
                                     m])))}))

(def fail (tree-m fail-p))

(defn == [u v]
  (tree-m
   (logic-arr. (fn [a]
                 (if-let [ap (unify a u v)]
                   (logic-m ap)
                   logic-zero))
               {:op :arrow-arr
                :tree (fn [g]
                        (tree-m (v/append-dg g {:id (v/genkey)
                                                :label (if @show-unify
                                                         (str u " == " v))
                                                })))})))

(defn all [& steps]
  (if (= (count steps) 1)
    (first steps)
    ;; TODO: maybe find a way to a/seq all the steps at once
    (m/bind (first steps)
            (m/chain (map (fn [step]
                            (fn [p]
                              (tree-cc
                               (fn [m c]
                                 (let [[step-p new-m] (build-tree step m c)]
                                   [(a/seq p step-p) new-m])))))
                          (rest steps))))))

(defn conde [& clauses]
  (tree-cc
   (fn [m c]
     (let [clauses (map #(first (build-tree (apply all %) m c)) clauses)
           clauses-p (apply a/par clauses)]
       [(logic-arr. (m/chain [(fn [s]
                                (logic-m (repeat (count clauses) s)))
                              clauses-p
                              (fn [ss]
                                (m/plus ss))])
                    (assoc (meta clauses-p)
                      :conde true))
        m]))))

(defn- lvar-bind [sym]
  ((juxt identity
         (fn [s] `(lvar '~s))) sym))

(defn- lvar-binds [syms]
  (mapcat lvar-bind syms))

(defmacro fresh [[& lvars] & goals]
  `(let [~@(lvar-binds lvars)]
     (clojure.core.logic/all ~@goals)))

;; =============================================================================
;; defining recursive functions

(defn recursive-p [sym]
  (logic-arr. (constantly logic-zero)
              {:self-recursive #{sym}
               (keyword sym) true
               :tree (fn [g]
                       (tree-cc
                        (fn [m c]
                          (assert (contains? m sym))
                          [(v/append-dg g {:id (v/genkey)
                                           :next [{:to (get m sym)}]}) m])))}))

(defn embed-tree [sym expr m c]
  (let [[p new-m] (build-tree expr
                              (conj m sym)
                              identity)]
    (if (and @prune-empty
               (= (get (meta p) :results 0) 0)
               (= (get (meta p) :self-recursive) #{sym}))
        [fail-p m]
        (c [(a/set-attr p
                        (keyword sym) true
                        :tree (fn [g]
                                (tree-cc
                                 (fn [m c]
                                   (let [root-id (v/genkey)
                                         new-g (v/append-dg g {:id (v/genkey)
                                                               :entry root-id
                                                               :exit root-id
                                                               root-id {:id root-id
                                                                        :label (str sym)}})]
                                     (make-graph p
                                                 new-g
                                                 (assoc m sym root-id)
                                                 (fn [[g m]]
                                                   (c [g (dissoc m sym)]))))))))
            (disj new-m sym)]))))

(defmacro defno [sym args & body]
  (let [expr (last body)
        body (butlast body)]
    `(defn ~sym ~args
       ~@body
       (let [~sym (constantly
                   (clojure.core.logic/tree-cc
                    (fn [m# c#]
                      [(clojure.core.logic/recursive-p '~sym) m#])))]
         (clojure.core.logic/tree-cc
          (fn [m# c#]
            (if (contains? m# '~sym)
             [(clojure.core.logic/recursive-p '~sym) m#]
             (clojure.core.logic/embed-tree '~sym ~expr m# c#))))))))
