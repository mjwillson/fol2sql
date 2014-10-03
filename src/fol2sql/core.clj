(ns fol2sql.core
  (:refer-clojure :exclude [gensym])
  (:require [clojure.core.match :refer [match]]
            [clojure.set :as set]
            [clojure.string :as str]
            [fol2sql.pretty-gensym :refer [gensym with-pretty-gensym]]))

(comment
  "FoL syntax in clojure"
  (foo x y) => "select x, y from foo"
  (exists [x] (foo x y)) => "select distinct y from foo"
  (and (foo x y) (bar y z)) => "select foo.x, foo.y, bar.z from foo join bar on foo.y = bar.y"
  (forall [x] (implies (man x) (mortal x)))
  =>  (not (exists [x] (and (man x) (not (mortal x))))) =>
  "select true where not exists (select x from man where x not in (select x from mortal))"


  ;; select the set of eaters who eat every food.
  (and
   (exists [x] (eats x y))
   (forall [x] (implies (food x)
                        (eats x y))))
  "select distinct y from eats where not exists
    (select food from food where food not in (select food from eats where eats.person = y)"

  Analogies
  First-order logic           / SQL
  Name of safe base predicate / Table
  instance of ^ in expression / Distinct alias of table
  Comparsion predicate        / Comparison operator
  Derived predicate           / Query, subquery or view
  Argument slot of predicate  / Column of table/view/subquery
  Variable                    / Set of equated columns of tables or their aliases
  and                         / and
  or                          / union, or
  not                         / not
  exists x                    / select distinct <all columns but x>, exists (select x from ...)
  forall x                    / not in (select ... where not exists (select x from ...))
  )

(defn desugar
  "Desugars the expression recursively to eliminate all implies and forall:

   (implies X Y) => (or (not X) Y)
   (forall [x] Y) => (not (exists [x] (not Y)))

   Most other functions assume desugared expressions as input."
  [expr]
  (match [expr]
         [(('and & clauses) :seq)]
         (apply list 'and (map desugar clauses))

         [(('or & clauses) :seq)]
         (apply list 'or (map desugar clauses))

         [(('implies hypothesis conclusion) :seq)]
         (list 'or (list 'not (desugar hypothesis)) (desugar conclusion))

         [(('not inner) :seq)]
         (list 'not (desugar inner))

         [(('exists [var] inner) :seq)]
         (list 'exists [var] (desugar inner))

         [(('forall [var] inner) :seq)]
         (list 'not (list 'exists [var] (list 'not (desugar inner))))

         [atom] atom))

(defn normalize
  " Applies these negation-related rewrite rules as far as possible:

     double negation elimination:
     (not (not X)) => X

     pushing negations inside and/or. (Note we could push them inside
     an exists, but that would create a forall which we want to
     avoid.)
     (not (and X Y)) => (or (not X) (not Y))
     (not (or X Y)) => (and (not X) (not Y))

     flattens nested ands and ors:
     (and (and x y) (and a b) c) => (and x y a b c)
     (or (or x y) (or a b) c) => (or x y a b c)

     Assumes input has been desguared.

     In the result, a not will only ever appear around an exists, or a base predicate.

     an and will never be nested directly inside an and, and likewise
     for or. Although note we don't go the whole hog and convert these
     boolean expressions to CNF or DNF."
  [expr]
  (match [expr]
         [(('and & clauses) :seq)]
         (apply list 'and (mapcat (fn [clause]
                                    (let [norm-clause (normalize clause)]
                                      (match [norm-clause]
                                             [(('and & nested-clauses) :seq)] nested-clauses
                                             :else [norm-clause])))
                                  clauses))

         [(('or & clauses) :seq)]
         (apply list 'or (mapcat (fn [clause]
                                   (let [norm-clause (normalize clause)]
                                     (match [norm-clause]
                                            [(('or & nested-clauses) :seq)] nested-clauses
                                            :else [norm-clause])))
                                 clauses))

         [(('not (('not inner) :seq)) :seq)]
         (normalize inner)

         [(('not (('and & clauses) :seq)) :seq)]
         (apply list 'or (map #(normalize (list 'not %)) clauses))

         [(('not (('or & clauses) :seq)) :seq)]
         (apply list 'and (map #(normalize (list 'not %)) clauses))

         [(('not inner) :seq)]
         (list 'not (normalize inner))

         [(('exists [var] inner) :seq)]
         (list 'exists [var] (normalize inner))

         [atom] atom))

(defn- constant?
  [expr]
  (or (string? expr) (number? expr)))

(defn free-vars
  "Returns the free variables in the expression.
   Performs some syntax checks while it's at it, in particular
   complains if a quantifier tries to close over a non-free variable.

   You can specify some constants, which will then not be treated as
   free in the expression."
  ([expr]
     (free-vars expr #{}))
  ([expr bound-vars]
     (match [expr]
            [(('and & clauses) :seq)]
            (apply set/union (map #(free-vars % bound-vars) clauses))

            [(('or & clauses) :seq)]
            (apply set/union (map #(free-vars % bound-vars) clauses))

            [(('implies hypothesis conclusion) :seq)]
            (set/union (free-vars hypothesis bound-vars)
                       (free-vars conclusion bound-vars))

            [(('not inner) :seq)]
            (free-vars inner bound-vars)

            [(('exists [var] inner) :seq)]
            (let [inner-free-vars (free-vars inner bound-vars)]
              (if (contains? inner-free-vars var)
                (set/difference inner-free-vars #{var})
                (throw (IllegalArgumentException.
                        (str "Quantifier can't close over variable " var
                             " which isn't free in expression " inner)))))

            [(('forall [var] inner) :seq)]
            (let [inner-free-vars (free-vars inner bound-vars)]
              (if (contains? inner-free-vars var)
                (set/difference inner-free-vars #{var})
                (throw (IllegalArgumentException.
                        (str "Quantifier can't close over variable " var
                             " which isn't free in expression " inner)))))

            [((predicate & arguments) :seq)]
            (if (empty? arguments)
              ;; we disallow these not because they're impossible to cope
              ;; with, but just because they're not very useful in
              ;; practise and they're fiddly to map to sql (would
              ;; probably need special-casing as boolean global variables
              ;; rather than tables)
              (throw (IllegalArgumentException.
                      (str "Nullary base predicates not supported: " expr)))
              (set/select (comp not constant?)
                          (set/difference (set arguments) bound-vars))))))

(def psuedosafe-base-predicate?
  "Special predicates which aren't in general represented by finite
  relations and aren't safe. (In sql, these are built-in comparison
p  operators rather than tables)"
  '#{= != < > >= <=})

(def to-negation
  '{= !=
    != =
    < >=
    > <=
    <= >
    >= <})

(defn- not-expr?
  "Returns the inner expression if this is a (not ...),
   otherwise nil."
  [expr]
  (match [expr]
         [(('not inner) :seq)] inner
         :else nil))

(defn safe-vars
  "An expression is safe if all its free variables are safe.

   It can also be pseudosafe -- not safe but able to be made safe if
   and-ed with safe expressions restricting any unsafe free variables.

   Finally an expression can be neither safe nor pseudosafe, if
   somewhere within it a variable which is not safe is closed over by
   a quantifier.

   This returns the free variables in an expression which are safe, and
   raises an exception if the expression is not psuedosafe."
  ([expr]
     (safe-vars expr #{}))
  ([expr bound-vars]
     (match [expr]
            [(('and & clauses) :seq)]
            ;; a var is safe in a conjunction iff it's safe in any
            ;; clause, and pseudo-safe in every clause.
            (apply set/union (map #(safe-vars % bound-vars) clauses))

            [(('or & clauses) :seq)]
            ;; a var is safe in a disjunction iff it's safe in every clause
            (apply set/intersection (map #(safe-vars % bound-vars) clauses))

            [(('not inner) :seq)]
            (do
              ;; raise exception if inner expression not psuedosafe:
              (safe-vars inner bound-vars)
              ;; no variable in a negation is safe:
              #{})

            [(('exists [var] inner) :seq)]
            ;; if the variable which the exists closes over is not
            ;; safe, the expression is neither safe nor psuedosafe.
            ;; otherwise, a variable is safe provided it's safe inside
            ;; the exists.
            (let [inner-safe-vars (safe-vars inner bound-vars)]
              (if (contains? inner-safe-vars var)
                (set/difference inner-safe-vars #{var})
                (throw (IllegalArgumentException.
                        (str "Quantifier closes over unsafe variable " var
                             " in expression " inner)))))

            [((predicate & arguments) :seq)]
            (if (psuedosafe-base-predicate? predicate)
              ;; a pseudosafe (but not safe) base predicate has no safe
              ;; free variables
              #{}
              ;; a safe base predicate has all its non-constant
              ;; arguments as safe variables.
              ;; (bound-vars aren't unsafe, but they're just not
              ;; free variables so there's no need to classify their
              ;; safety at all)
              (set/select (comp not constant?)
                          (set/difference (set arguments) bound-vars))))))

(defn safe?
  "Checks to see if a desguared and normalized expression is 'safe'
  and able to be mapped to relational algebra or sql queries.

  Safeness implies that there will be finitely many tuples satisfying
  it, but also a stronger property: that its interpretation doesn't
  depend on any assumptions about the full set of values in the domain
  which unrestrcited free variables range over.

  A safe expression will be either:

  * An 'or' whose clauses are safe expressions all over the same set
    of free variables

  * An 'and' where every free variable is included in at least one
    safe clause, and all clauses are at least pseudosafe.

  * A safe expression surrounded by an existential quantifier

  * A negation of a safe expression with no free variables

  * A safe base predicate

  A pseudosafe expression may not be safe, but is able to be made safe if
  and-ed with safe expressions restricting any unsafe free variables. It
  can be:

  * A safe expression
  * A pseudosafe base predicate like (> x y)
  * An exists closing over a safe variable in a pseudosafe expression
  * Any boolean expression built from pseudosafe expressions using not, and, or.

  This function will raise an exception if the expression is not even pseudosafe.

  Also recall that after the normalisation step, a not only ever appears before
  a base predicate or an exists, ands are not nested, ors are not nested."
  ([expr]
     (= (free-vars expr) (safe-vars expr)))
  ([expr bound-vars]
     (= (free-vars expr bound-vars) (safe-vars expr bound-vars))))

(defn- bound-var-or-const
  [expr bindings]
  (if (constant? expr)
    expr
    (bindings expr)))

;; clojure needs us to def ahead for mutual recursion
(def generate-select)
(def generate-and-clauses-select)

(defn- table-binding
  [safe-expr var-bindings]
  (-> [safe-expr]
      (match
       [(((:or 'and 'or 'not 'exists) & _) :seq)]
       ;; a subquery
       (let [alias (gensym 'subquery)]
         {:alias alias
          :expr (str "(" (generate-select safe-expr #{} var-bindings) ")")
          :var-to-column (->> (free-vars safe-expr (keys var-bindings))
                              ;; free variables in a subquery are
                              ;; selected in sort order
                              (sort)
                              ;; and the free variable names are
                              ;; reused as column names
                              (map (fn [var] {:var var :table-alias alias :column var})))
          ;; we leave any constants to be handled within the subquery,
          ;; we passed our bindings for them along to generate-select.
          :const-to-column {}})

       [((base-predicate & arguments) :seq)]
       (let [alias (gensym base-predicate)]
         {:alias alias
          :expr base-predicate
          ;; non-constant variable to the index of the slot in the base
          ;; predicate, which for now we use as a column name. so foo.0,
          ;; foo.1 etc
          :var-eq-column (keep-indexed
                          (fn [index arg]
                            (when-not (bound-var-or-const arg var-bindings)
                              {:var arg
                               :table-alias alias
                               :column (str "column_" index)}))
                          arguments)
          :column-eq-expr (keep-indexed
                           (fn [index arg]
                             (when-let [expr (bound-var-or-const arg var-bindings)]
                               {:expr expr
                                :table-alias alias
                                :column (str "column_" index)}))
                           arguments)}))))

(defn- column-equiv-classes
  [table-bindings]
  (->> table-bindings
       (mapcat :var-eq-column)
       (group-by :var)))

(defn- column-equiv-conds
  [var->cols]
  (mapcat (fn [[var columns]]
            (->> columns
                 (partition 2 1)
                 (map (fn [[c1 c2]]
                        (str (:table-alias c1) "." (:column c1)
                             " = "
                             (:table-alias c2) "." (:column c2)))))
            )
          var->cols))

(defn- column-eq-expr-conds
  [table-bindings]
  (->> table-bindings
       (mapcat :column-eq-expr)
       (map (fn [c]
              (str (:table-alias c) "." (:column c)
                   " = "
                   (:expr c))))))

(defn- from-expr
  [table-binding]
  (let [{:keys [expr alias]} table-binding]
    (if (= alias expr)
      expr
      (str expr " AS " alias))))

(defn- select-exprs
  [var->cols exclude-vars skip-as]
  (->> var->cols
       (sort-by first)
       (filter (fn [[var _]] (not (contains? exclude-vars var))))
       (map (fn [[var [col & _]]]
              (str (:table-alias col) "." (:column col)
                   (when-not skip-as (str " AS " var)))))))

(defn- column-var-bindings
  [var->cols]
  (reduce (fn [result [var [col & _]]]
            (assoc result var (str (:table-alias col) "." (:column col))))
          {}
          var->cols))

(defn- generate-condition
  "Converts a pseudosafe expression into an SQL condition"
  [expr var-bindings & [not]]
  (match [expr]
         [(('and & clauses) :seq)]
         (->> clauses
              (map #(generate-condition % var-bindings))
              (map #(str "(" % ")"))
              (str/join " AND "))

         [(('or & clauses) :seq)]
         (->> clauses
              (map #(generate-condition % var-bindings))
              (map #(str "(" % ")"))
              (str/join " OR "))


         [(('not inner) :seq)]
         ;; NOT can only happen outside a base pred or an exists. Both
         ;; these handle it specially:
         (generate-condition inner var-bindings true)

         [(('exists [var] inner) :seq)]
         (let [inner-free-vars (free-vars inner)
               exclude-vars (set/difference inner-free-vars #{var})]
           (str (when not "NOT ")
                "EXISTS ("
                (generate-select inner exclude-vars var-bindings
                                 :no-distinct-needed true :no-as-needed true)
                ")"))

         [((predicate & arguments) :seq)]
         (if (psuedosafe-base-predicate? predicate)
           ;; assume for now they're all binary operators which can be
           ;; negated:
           (str (bound-var-or-const (first arguments) var-bindings)
                " "
                (if not (to-negation predicate) predicate)
                " "
                (bound-var-or-const (second arguments) var-bindings))
           ;; a safe base predicate -- need to write out as an
           ;; EXISTS (SELECT true FROM table WHERE table.col = ...)
           ;; condition.
           ;; (We could also write this as an IN subquery, but EXISTS
           ;; works for zero arity too whereas IN doesn't)
           (str (when not "NOT ")
                "EXISTS ("
                (generate-and-clauses-select [expr] #{} var-bindings
                                             :no-distinct-needed true :no-as-needed true)
                ")"))))


(defn- generate-and-clauses-select
  [clauses exclude-vars var-bindings & {:keys [no-distinct-needed no-as-needed]}]
  (let [safe-clauses (filter #(safe? % (keys var-bindings)) clauses)
        pseudosafe-clauses (filter #(not (safe? % (keys var-bindings))) clauses)
        tables (map #(table-binding % var-bindings) safe-clauses)
        var->cols (column-equiv-classes tables)
        equiv-conds (column-equiv-conds var->cols)
        eq-conds (column-eq-expr-conds tables)
        new-var-bindings (merge
                          var-bindings
                          (column-var-bindings var->cols))
        other-conds (map
                     #(generate-condition % new-var-bindings)
                     pseudosafe-clauses)
        conds (concat equiv-conds eq-conds other-conds)
        from-exprs (map from-expr tables)
        select-exprs (select-exprs var->cols exclude-vars no-as-needed)]
    (str "SELECT "
         (when-not no-distinct-needed "DISTINCT ")
         (if (empty? select-exprs)
           "true"
           (str/join ", " select-exprs))
         " FROM "
         (str/join ", " from-exprs)
         (when-not (empty? conds)
           (str " WHERE " (str/join " AND " conds))))))

(defn- generate-select
  "Converts a safe expression to an SQL select query."
  ([expr]
     (generate-select expr #{} {}))
  ([expr exclude-vars var-bindings & {:keys [no-distinct-needed no-as-needed]}]
     (if (and (empty? (free-vars expr (keys var-bindings)))
              (or (psuedosafe-base-predicate? (first expr))
                  (#{'and 'or 'not} (first expr))))
       ;; Expressions with no free variables get implemented as SELECT
       ;; <boolean expr>, except where it's a base predicate filled
       ;; out with constants, in which case we use a more concise
       ;; SELECT DISTINCT true FROM base_pred. (better than SELECT
       ;; EXISTS (SELECT true FROM base_pred).
       (str "SELECT " (generate-condition expr var-bindings))
       ;; an expression with some free variables:
       (match [expr]
              [(('and & clauses) :seq)]
              (generate-and-clauses-select clauses exclude-vars var-bindings
                                           :no-distinct-needed no-distinct-needed
                                           :no-as-needed no-as-needed)

              [(('or & clauses) :seq)]
              (str/join " UNION " (map #(generate-select
                                         % exclude-vars var-bindings
                                         ;; UNION does a distinct for free
                                         :no-distinct-needed true)
                                       clauses))

              [(('exists [var] inner) :seq)]
              (generate-select inner (set/union exclude-vars #{var}) var-bindings
                               :no-distinct-needed no-distinct-needed
                               :no-as-needed no-as-needed)

              [base-predicate]
              (generate-and-clauses-select [base-predicate] exclude-vars var-bindings
                                           :no-distinct-needed no-distinct-needed
                                           :no-as-needed no-as-needed)))))

(defn to-sql
  [expr]
  (let [norm-expr (normalize (desugar expr))]
    (if (safe? norm-expr)
      (with-pretty-gensym
        (generate-select norm-expr))
      (throw (IllegalArgumentException. "expression not safe to convert to SQL")))))
