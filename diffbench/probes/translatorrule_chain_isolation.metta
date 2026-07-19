(= (let $pattern $value $body)
   (quote 999))

!(add-translator-rule! let)

!(chain 41 $x (+ $x 1))
