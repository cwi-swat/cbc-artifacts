(declare-const CollectionType Bool)
(declare-const Ordering Bool)
(declare-const Mutability Bool)
(declare-const UnaryCollection Bool)
(declare-const BinaryCollection Bool)

(assert (and CollectionType Ordering Mutability))
(assert (xor UnaryCollection BinaryCollection))

(assert (=> hashOfData unordered))

;(assert CollectionType)

(declare-const Test Int)

;(assert (and (> Test 10) (< Test 10)))



(check-sat)
(get-model)
