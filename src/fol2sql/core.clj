(ns fol2sql.core
  (:require [clojure.core.match :refer [match]]
            [clojure.set :as set]))

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

(defn free-vars
  "Returns the free variables in the expression.
   Performs some syntax checks while it's at it, in particular
   complains if a quantifier tries to close over a non-free variable"
   [expr]
  (match [expr]
         [(('and & clauses) :seq)]
         (apply set/union (map free-vars clauses))

         [(('or & clauses) :seq)]
         (apply set/union (map free-vars clauses))

         [(('implies hypothesis conclusion) :seq)]
         (set/union (free-vars hypothesis) (free-vars conclusion))

         [(('not inner) :seq)]
         (free-vars inner)

         [(('exists [var] inner) :seq)]
         (let [inner-free-vars (free-vars inner)]
           (if (contains? inner-free-vars var)
             (set/difference inner-free-vars #{var})
             (throw (IllegalArgumentException.
                     (str "Quantifier can't close over variable " var
                          " which isn't free in inner expression " inner)))))

         [(('forall [var] inner) :seq)]
         (let [inner-free-vars (free-vars inner)]
           (if (contains? inner-free-vars var)
             (set/difference inner-free-vars #{var})
             (throw (IllegalArgumentException.
                     (str "Quantifier can't close over variable " var
                          " which isn't free in inner expression " inner)))))

         [((predicate & arguments) :seq)]
         (if (empty? arguments)
           ;; we disallow these not because they're impossible to cope
           ;; with, but just because they're not very useful in
           ;; practise and they're fiddly to map to sql (would
           ;; probably need special-casing as boolean global variables
           ;; rather than tables)
           (throw (IllegalArgumentException.
                   (str "Nullary base predicates not supported: " expr)))
           (set arguments))))

(def psuedosafe-base-predicate?
  "Special predicates which aren't in general represented by finite
  relations and aren't safe. (In sql, these are built-in comparison
  operators rather than tables)"
  '#{= != < > >= <=})

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
  [expr]
  (match [expr]
         [(('and & clauses) :seq)]
         ;; a var is safe in a conjunction iff it's safe in any
         ;; clause, and pseudo-safe in every clause.
         (apply set/union (map safe-vars clauses))

         [(('or & clauses) :seq)]
         ;; a var is safe in a disjunction iff it's safe in every clause
         (apply set/intersection (map safe-vars clauses))

         [(('not inner) :seq)]
         (do
           ;; raise exception if inner expression not psuedosafe:
           (safe-vars inner)
           ;; no variable in a negation is safe:
           #{})

         [(('exists [var] inner) :seq)]
         ;; if the variable which the exists closes over is not
         ;; safe, the expression is neither safe nor psuedosafe.
         ;; otherwise, a variable is safe provided it's safe inside
         ;; the exists.
         (let [inner-safe-vars (safe-vars inner)]
           (if (contains? inner-safe-vars var)
             (set/difference inner-safe-vars #{var})
             (throw (IllegalArgumentException.
                     (str "Quantifier closes over unsafe variable " var
                          " in expression " inner)))))

         [((predicate & arguments) :seq)]
         (if (psuedosafe-base-predicate? predicate)
           ;; a pseudosafe (but not safe) base predicate has no safe
           ;; variables
           #{}
           ;; a safe base predicate has all its arguments as safe
           ;; variables
           (set arguments))))

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
  [expr]
  (= (free-vars expr) (safe-vars expr)))
