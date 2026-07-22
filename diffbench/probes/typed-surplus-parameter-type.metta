(: typed-surplus-parameter-type (-> Number Number Atom))
(= (typed-surplus-parameter-type $x) $x)

!(typed-surplus-parameter-type wrong-type)
