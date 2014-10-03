(ns fol2sql.pretty-gensym
  (:refer-clojure :exclude [gensym]))

(def ^:private ^:dynamic *gensym-table* nil)

(defn gensym
  [sym]
  (if *gensym-table*
    (if-let [count (*gensym-table* sym)]
      (do (set! *gensym-table* (update-in *gensym-table* [sym] inc))
          (symbol (str sym (inc count))))
      (do (set! *gensym-table* (assoc *gensym-table* sym 1))
          sym))
    (clojure.core/gensym sym)))

(defmacro with-pretty-gensym
  [& body]
  `(binding [*gensym-table* {}] ~@body))
