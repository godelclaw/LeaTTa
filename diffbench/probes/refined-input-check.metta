(: refined-id (-> Number Number))
(= (refined-id $value) $value)

!(refined-id 5)
!(refined-id "not-a-number")

(= (get-type $value)
   (catch (if (== (% $value 2) 0)
              EvenNumber)))

(: refined-even-id (-> EvenNumber EvenNumber))
(= (refined-even-id $value) $value)

!(refined-even-id 6)
!(refined-even-id 5)
