{-# OPTIONS --cubical-compatible --safe #-}

module BTree where

open import Level hiding (suc ; zero ; _⊔_ )

open import Data.Nat hiding (compare)
open import Data.Nat.Properties as NatProp
open import Data.Maybe
-- open import Data.Maybe.Properties
open import Data.Empty
open import Data.List
open import Data.Product

open import Data.Maybe.Properties
open import Data.List.Properties

open import Function as F hiding (const)

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import logic
open import nat


--
--
--  no children , having left node , having right node , having both
--
data bt {n : Level} (A : Set n) : Set n where
  leaf : bt A
  node :  (key : ℕ) → (value : A) →
    (left : bt A ) → (right : bt A ) → bt A

node-key : {n : Level} {A : Set n} → bt A → Maybe ℕ
node-key (node key _ _ _) = just key
node-key _ = nothing

node-value : {n : Level} {A : Set n} → bt A → Maybe A
node-value (node _ value _ _) = just value
node-value _ = nothing

bt-depth : {n : Level} {A : Set n} → (tree : bt A ) → ℕ
bt-depth leaf = 0
bt-depth (node key value t t₁) = suc (bt-depth t  ⊔ bt-depth t₁ )

bt-ne : {n : Level} {A : Set n} {key : ℕ} {value : A} {t t₁ : bt A} → ¬ ( leaf ≡ node key value t t₁ )
bt-ne {n} {A} {key} {value} {t} {t₁} ()

open import Data.Unit hiding ( _≟_ ) -- ;  _≤?_ ; _≤_)

tr< : {n : Level} {A : Set n} → (key : ℕ) → bt A → Set
tr< {_} {A} key leaf = ⊤
tr< {_} {A} key (node key₁ value tr tr₁) = (key₁ < key ) ∧ tr< key tr  ∧  tr< key tr₁

tr> : {n : Level} {A : Set n} → (key : ℕ) → bt A → Set
tr> {_} {A} key leaf = ⊤
tr> {_} {A} key (node key₁ value tr tr₁) = (key < key₁ ) ∧ tr> key tr  ∧  tr> key tr₁

--
--
data treeInvariant {n : Level} {A : Set n} : (tree : bt A) → Set n where
    t-leaf : treeInvariant leaf
    t-single : (key : ℕ) → (value : A) →  treeInvariant (node key value leaf leaf)
    t-right : (key key₁ : ℕ) → {value value₁ : A} → {t₁ t₂ : bt A} → key < key₁
       → tr> key t₁
       → tr> key t₂
       → treeInvariant (node key₁ value₁ t₁ t₂)
       → treeInvariant (node key value leaf (node key₁ value₁ t₁ t₂))
    t-left  : (key key₁ : ℕ) → {value value₁ : A} → {t₁ t₂ : bt A} → key < key₁
       → tr< key₁ t₁
       → tr< key₁ t₂
       → treeInvariant (node key value t₁ t₂)
       → treeInvariant (node key₁ value₁ (node key value t₁ t₂) leaf )
    t-node  : (key key₁ key₂ : ℕ) → {value value₁ value₂ : A} → {t₁ t₂ t₃ t₄ : bt A} → key < key₁ → key₁ < key₂
       → tr< key₁ t₁
       → tr< key₁ t₂
       → tr> key₁ t₃
       → tr> key₁ t₄
       → treeInvariant (node key value t₁ t₂)
       → treeInvariant (node key₂ value₂ t₃ t₄)
       → treeInvariant (node key₁ value₁ (node key value t₁ t₂) (node key₂ value₂ t₃ t₄))

--
--  stack always contains original top at end (path of the tree)
--
data stackInvariant {n : Level} {A : Set n}  (key : ℕ) : (top orig : bt A) → (stack  : List (bt A)) → Set n where
    s-nil :  {tree0 : bt A} → stackInvariant key tree0 tree0 (tree0 ∷ [])
    s-right :  (tree tree0 tree₁ : bt A) → {key₁ : ℕ } → {v1 : A } → {st : List (bt A)}
        → key₁ < key  →  stackInvariant key (node key₁ v1 tree₁ tree) tree0 st → stackInvariant key tree tree0 (tree ∷ st)
    s-left :  (tree₁ tree0 tree : bt A) → {key₁ : ℕ } → {v1 : A } → {st : List (bt A)}
        → key  < key₁ →  stackInvariant key (node key₁ v1 tree₁ tree) tree0 st → stackInvariant key tree₁ tree0 (tree₁ ∷ st)

data replacedTree  {n : Level} {A : Set n} (key : ℕ) (value : A)  : (before after : bt A ) → Set n where
    r-leaf : replacedTree key value leaf (node key value leaf leaf)
    r-node : {value₁ : A} → {t t₁ : bt A} → replacedTree key value (node key value₁ t t₁) (node key value t t₁)
    r-right : {k : ℕ } {v1 : A} → {t t1 t2 : bt A}
          → k < key →  replacedTree key value t2 t →  replacedTree key value (node k v1 t1 t2) (node k v1 t1 t)
    r-left : {k : ℕ } {v1 : A} → {t t1 t2 : bt A}
          → key < k →  replacedTree key value t1 t →  replacedTree key value (node k v1 t1 t2) (node k v1 t t2)

add< : { i : ℕ } (j : ℕ ) → i < suc i + j
add<  {i} j = begin
        suc i ≤⟨ m≤m+n (suc i) j ⟩
        suc i + j ∎  where open ≤-Reasoning

treeTest1  : bt ℕ
treeTest1  =  node 0 0 leaf (node 3 1 (node 2 5 (node 1 7 leaf leaf ) leaf) (node 5 5 leaf leaf))
treeTest2  : bt ℕ
treeTest2  =  node 3 1 (node 2 5 (node 1 7 leaf leaf ) leaf) (node 5 5 leaf leaf)

treeInvariantTest1  : treeInvariant treeTest1
treeInvariantTest1  = t-right _ _ (m≤m+n _ 2)
    ⟪ add< _ , ⟪ ⟪ add< _ , _ ⟫ , _ ⟫ ⟫
    ⟪ add< _ , ⟪ _ , _ ⟫ ⟫ (t-node _ _ _ (add< 0) (add< 1) ⟪ add< _ , ⟪ _ , _ ⟫ ⟫  _ _ _ (t-left _ _ (add< 0) _ _ (t-single 1 7)) (t-single 5 5) )

stack-top :  {n : Level} {A : Set n} (stack  : List (bt A)) → Maybe (bt A)
stack-top [] = nothing
stack-top (x ∷ s) = just x

stack-last :  {n : Level} {A : Set n} (stack  : List (bt A)) → Maybe (bt A)
stack-last [] = nothing
stack-last (x ∷ []) = just x
stack-last (x ∷ s) = stack-last s

stackInvariantTest1 : stackInvariant 4 treeTest2 treeTest1 ( treeTest2 ∷ treeTest1 ∷ [] )
stackInvariantTest1 = s-right _ _ _ (add< 3) (s-nil  )

si-property0 :  {n : Level} {A : Set n} {key : ℕ} {tree tree0 : bt A} → {stack  : List (bt A)} →  stackInvariant key tree tree0 stack → ¬ ( stack ≡ [] )
si-property0  (s-nil  ) ()
si-property0  (s-right _ _ _ x si) ()
si-property0  (s-left _ _ _ x si) ()


si-property1 :  {n : Level} {A : Set n} {key : ℕ} {tree tree0 tree1 : bt A} → {stack  : List (bt A)} →  stackInvariant key tree tree0 (tree1 ∷ stack)
   → tree1 ≡ tree
si-property1 {n} {A} {key} {tree} {tree0} {tree1} {stack} si = lem00 tree tree0 tree1 _ (tree1 ∷ stack) refl si where
    lem00 : (tree tree0 tree1 : bt A) → (stack  stack1 : List (bt A)) → tree1 ∷ stack ≡ stack1  →  stackInvariant key tree tree0 stack1 → tree1 ≡ tree
    lem00 tree .tree tree1 stack .(tree ∷ []) eq s-nil = ∷-injectiveˡ eq
    lem00 tree tree0 tree1 stack .(tree ∷ _) eq (s-right .tree .tree0 tree₁ x si) = ∷-injectiveˡ eq
    lem00 tree tree0 tree1 stack .(tree ∷ _) eq (s-left .tree .tree0 tree₁ x si) = ∷-injectiveˡ eq

si-property2 :  {n : Level} {A : Set n} {key : ℕ} {tree tree0 tree1 : bt A} → (stack  : List (bt A)) →  stackInvariant key tree tree0 (tree1 ∷ stack)
   → ¬ ( just leaf ≡ stack-last stack )
si-property2 {n} {A} {key} {tree} {tree0} {tree1} [] si ()
si-property2 {n} {A} {key} {tree} {tree0} {tree1} (x ∷ []) si eq with just-injective eq
... | refl = lem00 (tree1 ∷ leaf ∷ [])  refl si  where
    lem00 : (t : List (bt A)) → (tree1 ∷ leaf ∷ []) ≡ t → stackInvariant key tree tree0 t → ⊥
    lem00 .(tree ∷ []) () s-nil
    lem00 (tree ∷ _) () (s-right .tree .(node _ _ tree₁ tree) tree₁ x s-nil)
    lem00 (tree ∷ _) () (s-right .tree .tree0 tree₁ x (s-right .(node _ _ tree₁ tree) .tree0 tree₂ x₁ si2))
    lem00 (tree ∷ _) () (s-right .tree .tree0 tree₁ x (s-left .(node _ _ tree₁ tree) .tree0 tree₂ x₁ si2))
    lem00 (tree₁ ∷ _) () (s-left .tree₁ .(node _ _ tree₁ tree) tree x s-nil)
    lem00 (tree₁ ∷ _) () (s-left .tree₁ .tree0 tree x (s-right .(node _ _ tree₁ tree) .tree0 tree₂ x₁ si2))
    lem00 (tree₁ ∷ _) () (s-left .tree₁ .tree0 tree x (s-left .(node _ _ tree₁ tree) .tree0 tree₂ x₁ si2))
si-property2 {n} {A} {key} {tree} {tree0} {tree1} (x ∷ x₁ ∷ stack) si = lem00 (tree1 ∷ x ∷ x₁ ∷ stack) refl si where
    lem00 : (t : List (bt A)) → (tree1 ∷ x ∷ x₁ ∷ stack) ≡ t → stackInvariant key tree tree0 t → ¬ just leaf ≡ stack-last (x₁ ∷ stack)
    lem00 .(tree ∷ []) () s-nil
    lem00 (tree ∷ []) () (s-right .tree .tree0 tree₁ x si)
    lem00 (tree ∷ x₁ ∷ st) eq (s-right .tree .tree0 tree₁ x si) eq1 = si-property2 st si
         (subst (λ k → just leaf ≡ stack-last k ) (∷-injectiveʳ (∷-injectiveʳ eq)) eq1 )
    lem00 (tree ∷ []) () (s-left .tree .tree0 tree₁ x si)
    lem00 (tree₁ ∷ x₁ ∷  st) eq (s-left .tree₁ .tree0 tree x si) eq1 = si-property2 st si
         (subst (λ k → just leaf ≡ stack-last k ) (∷-injectiveʳ (∷-injectiveʳ eq)) eq1 )


-- We cannot avoid warning: -W[no]UnsupportedIndexedMatcin tree-inject
-- open import Function.Base using (_∋_; id; _∘_; _∘′_)
-- just-injective1 : {n : Level } {A : Set n} {x y : A } → (Maybe A ∋ just x) ≡ just y → x ≡ y
-- just-injective1 refl = refl

node-left : {n : Level} {A : Set n} → bt A → Maybe (bt A)
node-left (node _ _ left _) = just left
node-left _ = nothing

node-right : {n : Level} {A : Set n} → bt A → Maybe (bt A)
node-right (node _ _ _ right) = just right
node-right _ = nothing

--   lem00 = just-injective (cong node-key eq)

tree-injective-key : {n : Level} {A : Set n}
    → (tr0 tr1 : bt A) → tr0 ≡ tr1 → node-key tr0 ≡ node-key tr1
tree-injective-key {n} {A} tr0 tr1 eq = cong node-key eq

ti-property2 :  {n : Level} {A : Set n} {key : ℕ} {value : A} {tree1 left right : bt A}
   → tree1 ≡ node key value left right
   → left ≡ right
   → ( ¬ left  ≡ leaf ) ∨ ( ¬ right ≡ leaf )
   → ¬ treeInvariant tree1
ti-property2 {n} {A} {key} {value} {leaf} {left} {right} () eq1 x ti
ti-property2 {n} {A} {key} {value} {node key₁ value₁ leaf t₁} {left} {right} eq eq1 (case1 eq2) _
    = ⊥-elim ( eq2 (just-injective ( cong node-left (sym eq)  )))
ti-property2 {n} {A} {key} {value} {node key₁ value₁ leaf t₁} {left} {right} eq eq1 (case2 eq2) _
    = ⊥-elim ( eq2 (just-injective (trans (cong just (sym eq1)) ( cong node-left (sym eq)   ) ) ))
ti-property2 {n} {A} {key} {value} {node key₁ value₁ (node key₂ value₂ t t₂) leaf} {left} {right} eq eq1 (case1 eq2) _
    = ⊥-elim ( eq2 (just-injective (trans (cong just eq1) ( cong node-right (sym eq)   ) ) ))
ti-property2 {n} {A} {key} {value} {node key₁ value₁ (node key₂ value₂ t t₂) leaf} {left} {right} eq eq1 (case2 eq2) _
    = ⊥-elim ( eq2 (just-injective ( cong node-right (sym eq)  )))
ti-property2 {n} {A} {key} {value} {node key₂ value₂ (node key₁ value₁ t₁ t₂) (node key₃ value₃ t₃ t₄)} {left} {right} eq eq1 eq2 ti
     = ⊥-elim ( nat-≡< lem00 (lem03 _ _ _ refl lem01 lem02 ti) ) where
   lem01 : node key₁ value₁ t₁ t₂ ≡ left
   lem01 = just-injective ( cong node-left eq )
   lem02 : node key₃ value₃ t₃ t₄ ≡ right
   lem02 = just-injective ( cong node-right eq )
   lem00 : key₁ ≡ key₃
   lem00 = begin
      key₁ ≡⟨ just-injective ( begin
         just key₁  ≡⟨ cong node-key lem01 ⟩
         node-key left ≡⟨ cong node-key eq1 ⟩
         node-key right ≡⟨ cong node-key (sym lem02) ⟩
         just key₃ ∎ ) ⟩
      key₃ ∎ where open ≡-Reasoning
   lem03 :  (key₁ key₃ : ℕ) → (tr : bt A) → tr ≡ node key₂ value₂ (node key₁ value₁ t₁ t₂) (node key₃ value₃ t₃ t₄)
      → node key₁ value₁ t₁ t₂ ≡ left
      → node key₃ value₃ t₃ t₄ ≡ right
      → treeInvariant tr → key₁ < key₃
   lem03 _ _ .leaf () _ _ t-leaf
   lem03 _ _ .(node _ _ leaf leaf) () _ _ (t-single _ _)
   lem03 _ _ .(node _ _ (node _ _ _ _) leaf) () _ _ (t-left _ _ _ _ _ _)
   lem03 _ _ .(node _ _ leaf (node _ _ _ _)) () _ _ (t-right _ _ _ _ _ _)
   lem03 key₁ key₃ (node key _ (node _ _ _ _) (node _ _ _ _)) eq3 el er (t-node key₄ key₅ key₂ x x₁ x₂ x₃ x₄ x₅ ti ti₁) = lem04 where
       lem04 : key₁ < key₃
       lem04 = begin
         suc key₁ ≡⟨ cong suc ( just-injective (cong node-key (just-injective (cong node-left (sym eq3)) ) ) ) ⟩
         suc key₄ ≤⟨ <-trans x x₁ ⟩
         key₂ ≡⟨ just-injective (cong node-key (just-injective (cong node-right eq3) ) )  ⟩
         key₃ ∎ where open ≤-Reasoning

si-property-< :  {n : Level} {A : Set n} {key kp : ℕ} {value₂ : A} {tree orig tree₃ : bt A} → {stack  : List (bt A)}
   → ¬ ( tree ≡ leaf )
   → treeInvariant (node kp value₂ tree  tree₃ )
   → stackInvariant key tree orig (tree ∷ node kp value₂ tree  tree₃ ∷ stack)
   → key < kp
si-property-< {n} {A} {key} {kp} {value₂} {tree} {orig} {tree₃} {stack} ne ti si =
       lem00 (node kp value₂ tree  tree₃ ) (tree ∷ node kp value₂ tree  tree₃ ∷ stack) refl refl ti si where
    lem00 : (tree1 : bt A) → (st : List (bt A)) →  (tree1 ≡ (node kp value₂ tree  tree₃ )) → (st ≡ tree ∷ node kp value₂ tree  tree₃ ∷ stack)
       → treeInvariant tree1 → stackInvariant key tree orig st → key < kp
    lem00 tree1 .(tree ∷ []) teq () ti s-nil
    lem00 tree1 .(tree ∷ node key₁ v1 tree₁ tree ∷ []) teq seq ti₁ (s-right .tree .(node key₁ v1 tree₁ tree) tree₁ {key₁} {v1} x s-nil) = lem01 where
        lem02 :  node key₁ v1 tree₁ tree  ≡ node kp value₂ tree tree₃
        lem02 = ∷-injectiveˡ ( ∷-injectiveʳ seq )
        lem03 : tree₁ ≡ tree
        lem03 = just-injective (cong node-left lem02)
        lem01 : key < kp
        lem01 = ⊥-elim ( ti-property2 (sym lem02) lem03 (case2 ne) ti )
    lem00 tree1 .(tree ∷ node key₁ v1 tree₁ tree ∷ _) teq seq ti₁ (s-right .tree .orig tree₁ {key₁} {v1} x (s-right .(node _ _ tree₁ tree) .orig tree₂ {key₂} {v2} x₁ si)) = lem01 where
        lem02 :  node key₁ v1 tree₁ tree  ≡ node kp value₂ tree tree₃
        lem02 = ∷-injectiveˡ ( ∷-injectiveʳ seq )
        lem03 : tree₁ ≡ tree
        lem03 = just-injective (cong node-left lem02)
        lem01 : key < kp
        lem01 = ⊥-elim ( ti-property2 (sym lem02) lem03 (case2 ne) ti )
    lem00 tree1 (tree₂ ∷ node key₁ v1 tree₁ tree₂ ∷ _) teq seq ti₁ (s-right .tree₂ .orig tree₁ {key₁} {v1} x (s-left .(node _ _ tree₁ tree₂) .orig tree x₁ si)) = lem01 where
        lem02 :  node key₁ v1 tree₁ tree₂ ≡ node kp value₂ tree₂ tree₃
        lem02 = ∷-injectiveˡ ( ∷-injectiveʳ seq )
        lem03 : tree₁ ≡ tree₂
        lem03 = just-injective (cong node-left lem02 )
        lem01 : key < kp
        lem01 = ⊥-elim ( ti-property2 (sym lem02) lem03 (case2 ne) ti )
    lem00 tree1 (tree₁ ∷ _) teq seq ti₁ (s-left .tree₁ .(node _ _ tree₁ tree) tree {key₁} {v1} x s-nil) = subst( λ k → key < k ) lem03 x where
        lem03 : key₁ ≡ kp
        lem03 = just-injective (cong node-key (∷-injectiveˡ ( ∷-injectiveʳ seq )))
    lem00 tree1 (tree₁ ∷ _) teq seq ti₁ (s-left .tree₁ .orig tree {key₁} {v1} x (s-right .(node _ _ tree₁ tree) .orig tree₂ x₁ si)) = subst( λ k → key < k ) lem03 x where
        lem03 : key₁ ≡ kp
        lem03 = just-injective (cong node-key (∷-injectiveˡ ( ∷-injectiveʳ seq )))
    lem00 tree1 (tree₁ ∷ _) teq seq ti₁ (s-left .tree₁ .orig tree {key₁} {v1} x (s-left .(node _ _ tree₁ tree) .orig tree₂ x₁ si)) = subst( λ k → key < k ) lem03 x where
        lem03 : key₁ ≡ kp
        lem03 = just-injective (cong node-key (∷-injectiveˡ ( ∷-injectiveʳ seq )))

si-property-> :  {n : Level} {A : Set n} {key kp : ℕ} {value₂ : A} {tree orig tree₃ : bt A} → {stack  : List (bt A)}
   → ¬ ( tree ≡ leaf )
   → treeInvariant (node kp value₂ tree₃  tree )
   → stackInvariant key tree orig (tree ∷ node kp value₂ tree₃  tree ∷ stack)
   → kp < key
si-property-> {n} {A} {key} {kp} {value₂} {tree} {orig} {tree₃} {stack} ne ti si =
       lem00 (node kp value₂ tree₃  tree ) (tree ∷ node kp value₂ tree₃  tree ∷ stack) refl refl ti si where
    lem00 : (tree1 : bt A) → (st : List (bt A)) →  (tree1 ≡ (node kp value₂ tree₃  tree )) → (st ≡ tree ∷ node kp value₂ tree₃  tree ∷ stack)
       → treeInvariant tree1 → stackInvariant key tree orig st → kp < key
    lem00 tree1 .(tree ∷ []) teq () ti s-nil
    lem00 tree1 .(tree ∷ node key₁ v1 tree tree₁ ∷ []) teq seq ti₁ (s-left .tree .(node key₁ v1 tree tree₁) tree₁ {key₁} {v1} x s-nil) = lem01 where
        lem02 :  node key₁ v1 tree tree₁  ≡ node kp value₂ tree₃ tree
        lem02 = ∷-injectiveˡ ( ∷-injectiveʳ seq )
        lem03 : tree₁ ≡ tree
        lem03 = just-injective (cong node-right lem02)
        lem01 : kp < key
        lem01 = ⊥-elim ( ti-property2 (sym lem02) (sym lem03) (case1 ne) ti )
    lem00 tree1 .(tree ∷ node key₁ v1 tree tree₁ ∷ _) teq seq ti₁ (s-left .tree .orig tree₁ {key₁} {v1} x (s-left .(node _ _ tree tree₁) .orig tree₂ {key₂} {v2} x₁ si)) = lem01 where
        lem02 :  node key₁ v1 tree tree₁  ≡ node kp value₂ tree₃ tree
        lem02 = ∷-injectiveˡ ( ∷-injectiveʳ seq )
        lem03 : tree₁ ≡ tree
        lem03 = just-injective (cong node-right lem02)
        lem01 : kp < key
        lem01 = ⊥-elim ( ti-property2 (sym lem02) (sym lem03) (case1 ne) ti )
    lem00 tree1 (tree₂ ∷ node key₁ v1 tree₂ tree₁ ∷ _) teq seq ti₁ (s-left .tree₂ .orig tree₁ {key₁} {v1} x (s-right .(node _ _ tree₂ tree₁) .orig tree x₁ si)) = lem01 where
        lem02 :  node key₁ v1 tree₂ tree₁  ≡ node kp value₂ tree₃ tree₂
        lem02 = ∷-injectiveˡ ( ∷-injectiveʳ seq )
        lem03 : tree₁ ≡ tree₂
        lem03 = just-injective (cong node-right lem02)
        lem01 : kp < key
        lem01 = ⊥-elim ( ti-property2 (sym lem02) (sym lem03) (case1 ne) ti )
    lem00 tree1 (tree₁ ∷ _) teq seq ti₁ (s-right .tree₁ .(node _ _ tree tree₁) tree {key₁} {v1} x s-nil) = subst( λ k → k < key ) lem03 x where
        lem03 : key₁ ≡ kp
        lem03 = just-injective (cong node-key (∷-injectiveˡ ( ∷-injectiveʳ seq )))
    lem00 tree1 (tree₁ ∷ _) teq seq ti₁ (s-right .tree₁ .orig tree {key₁} {v1} x (s-left .(node _ _ tree tree₁) .orig tree₂ x₁ si)) = subst( λ k → k < key ) lem03 x where
        lem03 : key₁ ≡ kp
        lem03 = just-injective (cong node-key (∷-injectiveˡ ( ∷-injectiveʳ seq )))
    lem00 tree1 (tree₁ ∷ _) teq seq ti₁ (s-right .tree₁ .orig tree {key₁} {v1} x (s-right .(node _ _ tree tree₁) .orig tree₂ x₁ si)) = subst( λ k → k < key ) lem03 x where
        lem03 : key₁ ≡ kp
        lem03 = just-injective (cong node-key (∷-injectiveˡ ( ∷-injectiveʳ seq )))


si-property-last :  {n : Level} {A : Set n}  (key : ℕ) (tree tree0 : bt A) → (stack  : List (bt A)) →  stackInvariant key tree tree0 stack
   → stack-last stack ≡ just tree0
si-property-last {n} {A} key tree .tree .(tree ∷ []) s-nil = refl
si-property-last {n} {A} key tree tree0 (tree ∷ []) (s-right .tree .tree0 tree₁ x si) = ⊥-elim ( si-property0 si refl )
si-property-last {n} {A} key tree tree0 (tree ∷ x₁ ∷ st) (s-right .tree .tree0 tree₁ x si) = 
   si-property-last key _ tree0 (x₁ ∷ st)  si
si-property-last {n} {A} key tree tree0 (tree ∷ []) (s-left .tree .tree0 tree₁ x si) = ⊥-elim ( si-property0 si refl )
si-property-last {n} {A} key tree tree0 (tree ∷ x₁ ∷ st) (s-left .tree .tree0 tree₁ x si) = 
   si-property-last key _ tree0 (x₁ ∷ st)  si

si-property-pne :  {n : Level} {A : Set n}  {key key₁ : ℕ} {value₁ : A} (tree orig : bt A) → {left right x : bt A} → (stack  : List (bt A)) {rest : List (bt A)}
    → stack ≡ x ∷ node key₁ value₁ left right ∷ rest
    → stackInvariant key tree orig stack
    → ¬ ( key ≡ key₁ )
si-property-pne {_} {_} {key} {key₁} {value₁} tree orig {left} {right} (tree ∷ tree1 ∷ st) seq (s-right .tree .orig tree₁ {key₂} {v₂} x si) eq 
    = ⊥-elim ( nat-≡< lem00 x ) where
      lem01 : tree1 ≡ node key₂ v₂ tree₁ tree 
      lem01 = si-property1 si
      lem02 : node key₁ value₁ left right ≡ node key₂ v₂ tree₁ tree 
      lem02 = trans ( ∷-injectiveˡ (∷-injectiveʳ (sym seq) ) ) lem01
      lem00 : key₂ ≡ key
      lem00 = trans (just-injective (cong node-key (sym lem02))) (sym eq)
si-property-pne {_} {_} {key} {key₁} {value₁} tree orig {left} {right} (tree ∷ tree1 ∷ st) seq (s-left tree orig tree₁ {key₂} {v₂} x si) eq 
    = ⊥-elim ( nat-≡< (sym lem00) x ) where
      lem01 : tree1 ≡ node key₂ v₂ tree tree₁
      lem01 = si-property1 si
      lem02 : node key₁ value₁ left right ≡ node key₂ v₂ tree tree₁
      lem02 = trans ( ∷-injectiveˡ (∷-injectiveʳ (sym seq) ) ) lem01
      lem00 : key₂ ≡ key
      lem00 = trans (just-injective (cong node-key (sym  lem02))) (sym eq)
si-property-pne {_} {_} {key} {key₁} {value₁} tree .tree {left} {right} .(tree ∷ []) () s-nil eq


si-property-parent-node :  {n : Level} {A : Set n}  {key : ℕ}  (tree orig : bt A) {x : bt A}
    → (stack  : List (bt A)) {rest : List (bt A)}
    → stackInvariant key tree orig stack
    → ¬ ( stack ≡ x ∷ leaf ∷ rest )
si-property-parent-node {n} {A} tree .tree .(tree ∷ []) s-nil ()
si-property-parent-node {n} {A} tree .(node _ _ tree₁ tree) .(tree ∷ node _ _ tree₁ tree ∷ []) (s-right .tree .(node _ _ tree₁ tree) tree₁ x s-nil) ()
si-property-parent-node {n} {A} tree orig .(tree ∷ node _ _ tree₁ tree ∷ _) (s-right .tree .orig tree₁ x (s-right .(node _ _ tree₁ tree) .orig tree₂ x₁ si)) eq 
  = ⊥-elim ( bt-ne (sym (∷-injectiveˡ (∷-injectiveʳ eq)) ))
si-property-parent-node {n} {A} tree orig .(tree ∷ node _ _ tree₁ tree ∷ _) (s-right .tree .orig tree₁ x (s-left .(node _ _ tree₁ tree) .orig tree₂ x₁ si)) eq
  = ⊥-elim ( bt-ne (sym (∷-injectiveˡ (∷-injectiveʳ eq)) ))
si-property-parent-node {n} {A} tree .(node _ _ tree tree₁) .(tree ∷ node _ _ tree tree₁ ∷ []) (s-left .tree .(node _ _ tree tree₁) tree₁ x s-nil) ()
si-property-parent-node {n} {A} tree orig .(tree ∷ node _ _ tree tree₁ ∷ _) (s-left .tree .orig tree₁ x (s-right .(node _ _ tree tree₁) .orig tree₂ x₁ si)) eq 
  = ⊥-elim ( bt-ne (sym (∷-injectiveˡ (∷-injectiveʳ eq)) ))
si-property-parent-node {n} {A} tree orig .(tree ∷ node _ _ tree tree₁ ∷ _) (s-left .tree .orig tree₁ x (s-left .(node _ _ tree tree₁) .orig tree₂ x₁ si)) eq 
  = ⊥-elim ( bt-ne (sym (∷-injectiveˡ (∷-injectiveʳ eq)) ))


rt-property1 :  {n : Level} {A : Set n} (key : ℕ) (value : A) (tree tree1 : bt A ) → replacedTree key value tree tree1 → ¬ ( tree1 ≡ leaf )
rt-property1 {n} {A} key value .leaf .(node key value leaf leaf) r-leaf ()
rt-property1 {n} {A} key value .(node key _ _ _) .(node key value _ _) r-node ()
rt-property1 {n} {A} key value .(node _ _ _ _) _ (r-right x rt) = λ ()
rt-property1 {n} {A} key value .(node _ _ _ _) _ (r-left x rt) = λ ()

rt-property-leaf : {n : Level} {A : Set n} {key : ℕ} {value : A} {repl : bt A} → replacedTree key value leaf repl → repl ≡ node key value leaf leaf
rt-property-leaf {n} {A} {key} {value} {repl} rt = lem00 leaf refl rt where
   lem00 : (tree : bt A) → tree ≡ leaf → replacedTree key value tree repl → repl ≡ node key value leaf leaf
   lem00 leaf eq r-leaf = refl
   lem00 .(node key _ _ _) () r-node
   lem00 .(node _ _ _ _) () (r-right x rt)
   lem00 .(node _ _ _ _) () (r-left x rt)

--   rt-property-leaf' : {n : Level} {A : Set n} {key : ℕ} {value : A} {repl : bt A} → replacedTree key value leaf repl → repl ≡ node key value leaf leaf
--   rt-property-leaf' {n} {A} {key} {value} {.(node key value leaf leaf)} r-leaf = refl
--   rt-property-leaf' {n} {A} {key} {value} {.(node key value leaf leaf)} (r-right x rt) = ?
--   rt-property-leaf' {n} {A} {key} {value} {.(node key value leaf leaf)} (r-left x rt) = ?

rt-property-¬leaf : {n : Level} {A : Set n} {key : ℕ} {value : A} {tree : bt A} → ¬ replacedTree key value tree leaf
rt-property-¬leaf ()

rt-property-key : {n : Level} {A : Set n} {key key₂ key₃ : ℕ} {value value₂ value₃ : A} {left left₁ right₂ right₃ : bt A}
    →  replacedTree key value (node key₂ value₂ left right₂) (node key₃ value₃ left₁ right₃) → key₂ ≡ key₃
rt-property-key {n} {A} {key} {key₂} {key₃} {value} {value₂} {value₃} {left} {left₁} {right₂} {right₃} rt 
      = lem00 (node key₂ value₂ left right₂) (node key₃ value₃ left₁ right₃) refl refl rt where
    lem00 : (tree tree1 : bt A) → tree ≡ node key₂ value₂ left right₂ → tree1 ≡  node key₃ value₃ left₁ right₃ → replacedTree key value tree tree1 → key₂ ≡ key₃
    lem00 _ _ () eq2 r-leaf
    lem00 _ _ eq1 eq2 r-node = trans (just-injective (cong node-key (sym eq1))) (just-injective (cong node-key eq2))
    lem00 _ _ eq1 eq2 (r-right x rt1) = trans (just-injective (cong node-key (sym eq1))) (just-injective (cong node-key eq2))
    lem00 _ _ eq1 eq2 (r-left x rt1) = trans (just-injective (cong node-key (sym eq1))) (just-injective (cong node-key eq2))


open _∧_


depth-1< : {i j : ℕ} →   suc i ≤ suc (i Data.Nat.⊔ j )
depth-1< {i} {j} = s≤s (m≤m⊔n _ j)

depth-2< : {i j : ℕ} →   suc i ≤ suc (j Data.Nat.⊔ i )
depth-2< {i} {j} = s≤s (m≤n⊔m j i)

depth-3< : {i : ℕ } → suc i ≤ suc (suc i)
depth-3< {zero} = s≤s ( z≤n )
depth-3< {suc i} = s≤s (depth-3< {i} )


treeLeftDown  : {n : Level} {A : Set n} {k : ℕ} {v1 : A}  → (tree tree₁ : bt A )
      → treeInvariant (node k v1 tree tree₁)
      →      treeInvariant tree
treeLeftDown {n} {A} {k} {v1} tree tree₁ ti = lem00 (node k v1 tree tree₁) refl ti  where
    lem00 : ( tr : bt A ) → tr ≡ node k v1 tree tree₁ → treeInvariant tr → treeInvariant tree
    lem00 .leaf () t-leaf
    lem00 .(node key value leaf leaf) eq (t-single key value) = subst (λ k → treeInvariant k ) (just-injective (cong node-left eq)) t-leaf
    lem00 .(node key _ leaf (node key₁ _ _ _)) eq (t-right key key₁ x x₁ x₂ ti) = subst (λ k → treeInvariant k ) (just-injective (cong node-left eq)) t-leaf
    lem00 .(node key₁ _ (node key _ _ _) leaf) eq (t-left key key₁ x x₁ x₂ ti) = subst (λ k → treeInvariant k ) (just-injective (cong node-left eq)) ti
    lem00 .(node key₁ _ (node key _ _ _) (node key₂ _ _ _)) eq (t-node key key₁ key₂ x x₁ x₂ x₃ x₄ x₅ ti ti₁) = subst (λ k → treeInvariant k ) (just-injective (cong node-left eq)) ti

treeRightDown  : {n : Level} {A : Set n} {k : ℕ} {v1 : A}  → (tree tree₁ : bt A )
      → treeInvariant (node k v1 tree tree₁)
      →      treeInvariant tree₁
treeRightDown {n} {A} {k} {v1} tree tree₁ ti = lem00 (node k v1 tree tree₁) refl ti  where
    lem00 : ( tr : bt A ) → tr ≡ node k v1 tree tree₁ → treeInvariant tr → treeInvariant tree₁
    lem00 .leaf () t-leaf
    lem00 .(node key value leaf leaf) eq (t-single key value) = subst (λ k → treeInvariant k ) (just-injective (cong node-right eq)) t-leaf
    lem00 .(node key _ leaf (node key₁ _ _ _)) eq (t-right key key₁ x x₁ x₂ ti) = subst (λ k → treeInvariant k ) (just-injective (cong node-right eq)) ti
    lem00 .(node key₁ _ (node key _ _ _) leaf) eq (t-left key key₁ x x₁ x₂ ti) = subst (λ k → treeInvariant k ) (just-injective (cong node-right eq)) t-leaf
    lem00 .(node key₁ _ (node key _ _ _) (node key₂ _ _ _)) eq (t-node key key₁ key₂ x x₁ x₂ x₃ x₄ x₅ ti ti₁) = subst (λ k → treeInvariant k ) (just-injective (cong node-right eq)) ti₁


ti-property1 :  {n : Level} {A : Set n} {key₁ : ℕ} {value₂ : A} {left right : bt A} → treeInvariant (node key₁ value₂  left right ) →   tr< key₁ left ∧  tr> key₁ right
ti-property1 {n} {A} {key₁} {value₂} {left} {right} ti = lem00 key₁ (node key₁ value₂ left right) refl ti where
    lem00 : (key₁ : ℕ) → ( tree : bt A ) → tree ≡ node key₁ value₂ left right → treeInvariant tree → tr< key₁ left ∧  tr> key₁ right
    lem00 - .leaf () t-leaf
    lem00 key₁ .(node key value leaf leaf) eq (t-single key value) = subst₂ (λ j k → tr< key₁ j ∧ tr> key₁ k ) lem01 lem02 ⟪ tt , tt ⟫ where
         lem01 : leaf ≡ left
         lem01 = just-injective (cong node-left eq)
         lem02 : leaf ≡ right
         lem02 = just-injective (cong node-right eq)
    lem00 key₂ .(node key _ leaf (node key₁ _ _ _)) eq (t-right key key₁ {value} {value₁} {t₁} {t₂} x x₁ x₂ ti) 
         = subst₂ (λ j k → tr< key₂ j ∧ tr> key₂ k ) lem01 lem02 ⟪ tt , ⟪ subst (λ k → k < key₁) lem04 x , 
              ⟪ subst (λ k → tr> k t₁) lem04 x₁ , subst (λ k → tr> k t₂) lem04 x₂ ⟫  ⟫ ⟫ where
         lem01 : leaf ≡ left
         lem01 = just-injective (cong node-left eq)
         lem02 : node key₁ value₁ t₁ t₂ ≡ right
         lem02 = just-injective (cong node-right eq)
         lem04 : key ≡ key₂
         lem04 = just-injective (cong node-key eq)
    lem00 key₂ .(node key₁ _ (node key _ _ _) leaf) eq (t-left key key₁ {value} {value₁} {t₁} {t₂} x x₁ x₂ ti) 
         = subst₂ (λ j k → tr< key₂ j ∧ tr> key₂ k ) lem02 lem01 ⟪ ⟪ subst (λ k → key < k) lem04 x , 
              ⟪ subst (λ k → tr< k t₁) lem04 x₁  , subst (λ k → tr< k t₂) lem04 x₂  ⟫  ⟫ , tt ⟫ where
         lem01 : leaf ≡ right
         lem01 = just-injective (cong node-right eq)
         lem02 : node key value t₁ t₂ ≡ left
         lem02 = just-injective (cong node-left eq)
         lem04 : key₁ ≡ key₂
         lem04 = just-injective (cong node-key eq)
    lem00 key₂ .(node key₁ _ (node key _ _ _) (node key₃ _ _ _)) eq (t-node key key₁ key₃ {value} {value₁} {value₂} 
      {t₁} {t₂} {t₃} {t₄} x x₁ x₂ x₃ x₄ x₅ ti ti₁) 
        = subst₂ (λ j k → tr< key₂ j ∧ tr> key₂ k ) lem01 lem02 ⟪ ⟪ subst (λ k → key < k) lem04 x , 
             ⟪ subst (λ k → tr< k t₁) lem04 x₂ , subst (λ k → tr< k t₂) lem04 x₃ ⟫ ⟫   
           , ⟪ subst (λ k → k < key₃) lem04 x₁  , ⟪  subst (λ k → tr> k t₃) lem04 x₄   , subst (λ k → tr> k t₄) lem04 x₅  ⟫  ⟫ ⟫ where
         lem01 : node key value t₁ t₂  ≡ left
         lem01 = just-injective (cong node-left eq)
         lem02 : node key₃ value₂ t₃ t₄  ≡ right
         lem02 = just-injective (cong node-right eq)
         lem04 : key₁ ≡ key₂
         lem04 = just-injective (cong node-key eq)




findP : {n m : Level} {A : Set n} {t : Set m} → (key : ℕ) → (tree tree0 : bt A ) → (stack : List (bt A))
           →  treeInvariant tree ∧ stackInvariant key tree tree0 stack
           → (next : (tree1 : bt A) → (stack : List (bt A)) → treeInvariant tree1 ∧ stackInvariant key tree1 tree0 stack → bt-depth tree1 < bt-depth tree   → t )
           → (exit : (tree1 : bt A) → (stack : List (bt A)) → treeInvariant tree1 ∧ stackInvariant key tree1 tree0 stack
                 → (tree1 ≡ leaf ) ∨ ( node-key tree1 ≡ just key )  → t ) → t
findP key leaf tree0 st Pre _ exit = exit leaf st Pre (case1 refl)
findP key (node key₁ v1 tree tree₁) tree0 st Pre next exit with <-cmp key key₁
findP key n tree0 st Pre _ exit | tri≈ ¬a refl ¬c = exit n st Pre (case2 refl)
findP {n} {_} {A} key (node key₁ v1 tree tree₁) tree0 st  Pre next _ | tri< a ¬b ¬c = next tree (tree ∷ st)
       ⟪ treeLeftDown tree tree₁ (proj1 Pre)  , findP1 a st (proj2 Pre) ⟫ depth-1< where
   findP1 : key < key₁ → (st : List (bt A)) →  stackInvariant key (node key₁ v1 tree tree₁) tree0 st → stackInvariant key tree tree0 (tree ∷ st)
   findP1 a [] si = ⊥-elim ( si-property0 si refl )
   findP1 a (x ∷ st) si = s-left _ _ _ a si
findP key n@(node key₁ v1 tree tree₁) tree0 st Pre next _ | tri> ¬a ¬b c = next tree₁ (tree₁ ∷ st) ⟪ treeRightDown tree tree₁ (proj1 Pre) , s-right _ _ _ c (proj2 Pre) ⟫ depth-2<

replaceTree1 : {n  : Level} {A : Set n} {t t₁ : bt A } → ( k : ℕ ) → (v1 value : A ) →  treeInvariant (node k v1 t t₁) → treeInvariant (node k value t t₁)
replaceTree1 {n} {A} {t} {t₁} k v1 value ti = lem00 (node k v1 t t₁) refl ti where
   lem00 : (tree : bt A) → tree ≡ node k v1 t t₁ → treeInvariant tree → treeInvariant (node k value t t₁)
   lem00 _ () t-leaf
   lem00 .(node key v1 leaf leaf) eq (t-single key v1) = subst₂ (λ j k₁ → treeInvariant (node k value j k₁)) lem01 lem02 (t-single k value) where
       lem01 : leaf ≡ t
       lem01 = just-injective (cong node-left eq)
       lem02 : leaf ≡ t₁
       lem02 = just-injective (cong node-right eq)
   lem00 .(node key _ leaf (node key₁ _ _ _)) eq (t-right key key₁ {value} {value₁} {t₁} {t₃} x x₁ x₂ ti) 
      = subst₂ (λ j k₁ → treeInvariant (node _ _ j k₁)) lem01 lem02 (t-right _ _ (subst (λ j → j < key₁) lem03 x)  
            (subst (λ j → tr> j t₁ ) lem03 x₁) (subst (λ j → tr> j t₃ ) lem03 x₂) ti) where
       lem01 : leaf ≡ t
       lem01 = just-injective (cong node-left eq)
       lem02 : node key₁ value₁ t₁ t₃ ≡ _
       lem02 = just-injective (cong node-right eq)
       lem03 : key ≡ k
       lem03 = just-injective (cong node-key eq)
   lem00 .(node key₁ _ (node key _ _ _) leaf) eq (t-left key key₁  {value} {value₁} {t₁} {t₃} x x₁ x₂ ti) 
      = subst₂ (λ j k₁ → treeInvariant (node _ _ j k₁)) lem02 lem01 (t-left _ _ (subst (λ j → key < j) lem03 x)  
            (subst (λ j → tr< j t₁ ) lem03 x₁) (subst (λ j → tr< j t₃ ) lem03 x₂) ti) where
       lem01 : leaf ≡ _
       lem01 = just-injective (cong node-right eq)
       lem02 : node key value t₁ t₃ ≡ _
       lem02 = just-injective (cong node-left eq)
       lem03 : key₁ ≡ k
       lem03 = just-injective (cong node-key eq)
   lem00 .(node key₁ _ (node key _ _ _) (node key₃ _ _ _)) eq (t-node key key₁ key₃  {value} {value₁} {value₂} 
          {t₁} {t₂} {t₃} {t₄}  x x₁ x₂ x₃ x₄ x₅ ti ti₁) 
      = subst₂ (λ j k₁ → treeInvariant (node _ _ j k₁)) lem01 lem02 (t-node _ _ _ (subst (λ j → key < j) lem04 x)  (subst (λ j → j < key₃)  lem04 x₁) 
          (subst (λ j → tr< j t₁ ) lem04 x₂ ) 
          (subst (λ j → tr< j _ ) lem04 x₃ ) 
          (subst (λ j → tr> j _ ) lem04 x₄ ) 
          (subst (λ j → tr> j _ ) lem04 x₅ ) 
             ti ti₁ ) where
       lem01 : node key value t₁ t₂  ≡ _
       lem01 = just-injective (cong node-left eq)
       lem02 : node _ value₂ t₃ t₄  ≡ _
       lem02 = just-injective (cong node-right eq)
       lem04 : key₁ ≡ _
       lem04 = just-injective (cong node-key eq)

open import Relation.Binary.Definitions

child-replaced :  {n : Level} {A : Set n} (key : ℕ)   (tree : bt A) → bt A
child-replaced key leaf = leaf
child-replaced key (node key₁ value left right) with <-cmp key key₁
... | tri< a ¬b ¬c = left
... | tri≈ ¬a b ¬c = node key₁ value left right
... | tri> ¬a ¬b c = right

child-replaced-left :  {n : Level} {A : Set n} {key key₁ : ℕ}  {value : A}  {left right : bt A}
   → key < key₁
   → child-replaced key (node key₁ value left right) ≡ left
child-replaced-left {n} {A} {key} {key₁} {value} {left} {right} lt = ch00 (node key₁ value left right) refl lt where
     ch00 : (tree : bt A) → tree ≡ node key₁ value left right → key < key₁ → child-replaced key (node key₁ value left right) ≡ left
     ch00 tree eq lt1 with <-cmp key key₁
     ... | tri< a ¬b ¬c = refl
     ... | tri≈ ¬a b ¬c = ⊥-elim (¬a lt1)
     ... | tri> ¬a ¬b c = ⊥-elim (¬a lt1)

child-replaced-right :  {n : Level} {A : Set n} {key key₁ : ℕ}  {value : A}  {left right : bt A}
   → key₁ < key
   → child-replaced key (node key₁ value left right) ≡ right
child-replaced-right {n} {A} {key} {key₁} {value} {left} {right} lt = ch00 (node key₁ value left right) refl lt where
     ch00 : (tree : bt A) → tree ≡ node key₁ value left right → key₁ < key → child-replaced key (node key₁ value left right) ≡ right
     ch00 tree eq lt1 with <-cmp key key₁
     ... | tri< a ¬b ¬c = ⊥-elim (¬c lt1)
     ... | tri≈ ¬a b ¬c = ⊥-elim (¬c lt1)
     ... | tri> ¬a ¬b c = refl

child-replaced-eq :  {n : Level} {A : Set n} {key key₁ : ℕ}  {value : A}  {left right : bt A}
   → key₁ ≡ key
   → child-replaced key (node key₁ value left right) ≡ node key₁ value left right
child-replaced-eq {n} {A} {key} {key₁} {value} {left} {right} keq = ch00 (node key₁ value left right) refl keq where
     ch00 : (tree : bt A) → tree ≡ node key₁ value left right → key₁ ≡ key → child-replaced key (node key₁ value left right) ≡ node key₁ value left right
     ch00 tree eq keq with <-cmp key key₁
     ... | tri< a ¬b ¬c = ⊥-elim (¬b (sym keq))
     ... | tri≈ ¬a b ¬c = refl
     ... | tri> ¬a ¬b c = ⊥-elim (¬b (sym keq))

open _∧_


open _∧_

record IsNode {n : Level} {A : Set n} (t : bt A) : Set (Level.suc n) where
  field
    key : ℕ
    value : A
    left : bt A
    right : bt A
    t=node : t ≡ node key value left right

node→leaf∨IsNode : {n : Level} {A : Set n} → (t : bt A ) → (t ≡ leaf) ∨ IsNode t
node→leaf∨IsNode leaf = case1 refl
node→leaf∨IsNode (node key value t t₁) = case2 record { key = key ; value = value ; left = t ; right = t₁ ; t=node = refl }

IsNode→¬leaf : {n : Level} {A : Set n} (t : bt A) → IsNode t →  ¬ (t ≡ leaf)
IsNode→¬leaf .(node key value left right) record { key = key ; value = value ; left = left ; right = right ; t=node = refl } ()


ri-tr>  : {n : Level} {A : Set n}  → (tree repl : bt A) → (key key₁ : ℕ) → (value : A)
     → replacedTree key value tree repl → key₁ < key → tr> key₁ tree → tr> key₁ repl
ri-tr> .leaf .(node key value leaf leaf) key key₁ value r-leaf a tgt = ⟪ a , ⟪ tt , tt ⟫ ⟫
ri-tr> .(node key _ _ _) .(node key value _ _) key key₁ value r-node a tgt = ⟪ a , ⟪ proj1 (proj2 tgt) , proj2 (proj2 tgt) ⟫ ⟫
ri-tr> .(node _ _ _ _) .(node _ _ _ _) key key₁ value (r-right x ri) a tgt = ⟪ proj1 tgt , ⟪ proj1 (proj2 tgt) , ri-tr> _ _ _ _ _ ri a (proj2 (proj2 tgt)) ⟫ ⟫
ri-tr> .(node _ _ _ _) .(node _ _ _ _) key key₁ value (r-left x ri) a tgt = ⟪ proj1 tgt , ⟪  ri-tr> _ _ _ _ _ ri a (proj1 (proj2 tgt)) , proj2 (proj2 tgt)  ⟫ ⟫

ri-tr<  : {n : Level} {A : Set n}  → (tree repl : bt A) → (key key₁ : ℕ) → (value : A)
     → replacedTree key value tree repl → key < key₁ → tr< key₁ tree → tr< key₁ repl
ri-tr< .leaf .(node key value leaf leaf) key key₁ value r-leaf a tgt = ⟪ a , ⟪ tt , tt ⟫ ⟫
ri-tr< .(node key _ _ _) .(node key value _ _) key key₁ value r-node a tgt = ⟪ a , ⟪ proj1 (proj2 tgt) , proj2 (proj2 tgt) ⟫ ⟫
ri-tr< .(node _ _ _ _) .(node _ _ _ _) key key₁ value (r-right x ri) a tgt = ⟪ proj1 tgt , ⟪ proj1 (proj2 tgt) , ri-tr< _ _ _ _ _ ri a (proj2 (proj2 tgt)) ⟫ ⟫
ri-tr< .(node _ _ _ _) .(node _ _ _ _) key key₁ value (r-left x ri) a tgt = ⟪ proj1 tgt , ⟪  ri-tr< _ _ _ _ _ ri a (proj1 (proj2 tgt)) , proj2 (proj2 tgt)  ⟫ ⟫

<-tr>  : {n : Level} {A : Set n}  → {tree : bt A} → {key₁ key₂ : ℕ} → tr> key₁ tree → key₂ < key₁  → tr> key₂ tree
<-tr> {n} {A} {leaf} {key₁} {key₂} tr lt = tt
<-tr> {n} {A} {node key value t t₁} {key₁} {key₂} tr lt = ⟪ <-trans lt (proj1 tr) , ⟪ <-tr> (proj1 (proj2 tr)) lt , <-tr> (proj2 (proj2 tr)) lt ⟫ ⟫

>-tr<  : {n : Level} {A : Set n}  → {tree : bt A} → {key₁ key₂ : ℕ} → tr< key₁ tree → key₁ < key₂  → tr< key₂ tree
>-tr<  {n} {A} {leaf} {key₁} {key₂} tr lt = tt
>-tr<  {n} {A} {node key value t t₁} {key₁} {key₂} tr lt = ⟪ <-trans (proj1 tr) lt , ⟪ >-tr< (proj1 (proj2 tr)) lt , >-tr< (proj2 (proj2 tr)) lt ⟫ ⟫

RTtoTI0  : {n : Level} {A : Set n}  → (tree repl : bt A) → (key : ℕ) → (value : A) → treeInvariant tree
     → replacedTree key value tree repl → treeInvariant repl
RTtoTI0 {n} {A} tree repl key value ti1 rt1 = lem00 tree _ _ _ refl ti1 rt1 where
   lem00 : (tree tree1 : bt A) → (key : ℕ) → (value : A) → tree ≡ tree1 → treeInvariant tree  → replacedTree key value tree1 repl → treeInvariant repl
   lem00 tree .leaf key value eq ti r-leaf = t-single key value
   lem00 tree .(node key _ _ _) key value eq ti r-node = replaceTree1 key _ _ (subst (λ k → treeInvariant k) eq ti)
   lem00 tree .(node _ _ _ _) key value eq1 ti (r-right {k₁} {v₁} {t₁} {t₂} {t₃} x rt) = lem03 _ ti eq1 lem02 rt where
       lem01 : treeInvariant t₃
       lem01 = treeRightDown _ _ (subst (λ k → treeInvariant k ) eq1 ti )
       lem02 : treeInvariant t₁
       lem02 = RTtoTI0 _ t₁ key value lem01 rt
       lem03 : (tree : bt A) → treeInvariant tree → tree ≡ node k₁ v₁ t₂ t₃  → treeInvariant t₁ 
            → replacedTree _ _ t₃ t₁ → treeInvariant (node k₁ v₁ t₂ t₁)
       lem03 tree ti eq2 ti1 r-leaf = lem04 t₂ _ refl (subst (λ k → treeInvariant k) eq2 ti) where
           lem04 : (t₂ tree : bt A) → tree ≡ node k₁ v₁ t₂ leaf → treeInvariant tree → treeInvariant (node k₁ v₁ t₂ (node key value leaf leaf))
           lem04 t₂ _ () t-leaf
           lem04 leaf _ eq (t-single key value) = t-right _ _ x _ _ (t-single _ _)
           lem04 (node k v tl tr) _ () (t-single key value)
           lem04 leaf _ () (t-left key key₁ x x₁ x₂ ti)
           lem04 (node key₂ value t₂ t₃) _ eq (t-left key key₁ {_} {_} {t₄} {t₅} x₀ x₁ x₂ ti) = 
               t-node _ _ _ lem06 x lem07 lem08 _ _ (subst (λ k → treeInvariant k) lem05 ti) (t-single _ _) where
                  lem05 : node key _ t₄ t₅ ≡ node key₂ value t₂ t₃
                  lem05 = just-injective (cong node-left eq)
                  lem06 : key₂ < k₁
                  lem06 = subst₂ (λ j k → j < k ) (just-injective (cong node-key lem05)) (just-injective (cong node-key eq)) x₀
                  lem07 : tr< k₁ t₂
                  lem07 = subst₂ (λ j k → tr< j k ) (just-injective (cong node-key eq)) (just-injective (cong node-left lem05)) x₁
                  lem08 : tr< k₁ t₃
                  lem08 = subst₂ (λ j k → tr< j k ) (just-injective (cong node-key eq)) (just-injective (cong node-right lem05)) x₂
           lem04 t₂ _ () (t-right key key₁ x x₁ x₂ ti)
           lem04 t₂ _ () (t-node key key₁ key₂ x₁ x₂ x₃ x₄ x₅ x₆ ti ti₁)
       lem03 tree ti eq2 ti1 (r-node {value₁} {t} {t₁}) = lem04 t₂ _ refl (subst (λ k → treeInvariant k) eq2 ti) where
           lem04 : (t₂ tree : bt A) → tree ≡ node k₁ v₁ t₂ (node key value₁ t t₁) → treeInvariant tree → treeInvariant (node k₁ v₁ t₂ (node key value t t₁ ))
           lem04 t₂ .leaf () t-leaf
           lem04 t₂ .(node key value leaf leaf) () (t-single key value)
           lem04 (node k v _ _) .(node key value₂ leaf (node key₁ _ t₄ t₅)) () (t-right key key₁ {value₂} {_} {t₄} {t₅} x x₁ x₂ ti)
           lem04 leaf .(node key value₂ leaf (node key₁ _ t₄ t₅)) eq (t-right key key₁ {value₂} {_} {t₄} {t₅} x₀ x₁ x₂ ti) = t-right _ _ x lem05 lem06 ti1 where
                  lem05 : tr> k₁ t
                  lem05 = subst₂ (λ j k → tr> j k) (just-injective (cong node-key eq)) (just-injective (cong node-left ( just-injective (cong node-right eq))))  x₁
                  lem06 : tr> k₁ t₁
                  lem06 = subst₂ (λ j k → tr> j k) (just-injective (cong node-key eq)) (just-injective (cong node-right ( just-injective (cong node-right eq))))  x₂
           lem04 t₂ _ () (t-left key key₁ x x₁ x₂ ti)
           lem04 leaf .(node key₁ _ (node key _ _ _) (node key₂ _ _ _)) () (t-node key key₁ key₂ x x₁ x₂ x₃ x₄ x₅ ti ti₁)
           lem04 (node key₃ value t₂ t₃) .(node key₁ _ (node key _ _ _) (node key₂ _ _ _)) eq (
               t-node key key₁ key₂ {v₁} {v₂} {t₄} {t₅} {t₆} {t₇} {t₈} x x₁ x₂ x₃ x₄ x₅ ti ti₁) 
                 = t-node _ _ _ lem06 lem07 lem08 lem09 lem10 lem11 (subst (λ k → treeInvariant k) lem05 ti) ti1 where
                  lem05 : node key v₁ t₅ t₆ ≡ node key₃ value t₂ t₃
                  lem05 = just-injective (cong node-left eq)
                  lem06 :  key₃ < k₁
                  lem06 = subst₂ (λ j k → j < k ) (just-injective (cong node-key lem05)) (just-injective (cong node-key eq)) x
                  lem07 : k₁ < _
                  lem07 = subst₂ (λ j k → j < k ) (just-injective (cong node-key eq)) (just-injective (cong node-key ( just-injective (cong node-right eq)))) x₁
                  lem08 : tr< k₁ t₂
                  lem08 = subst₂ (λ j k → tr< j k ) (just-injective (cong node-key eq)) (just-injective (cong node-left ( just-injective (cong node-left eq)))) x₂
                  lem09 : tr< k₁ t₃
                  lem09 = subst₂ (λ j k → tr< j k ) (just-injective (cong node-key eq)) (just-injective (cong node-right ( just-injective (cong node-left eq)))) x₃
                  lem10 : tr> k₁ t
                  lem10 = subst₂ (λ j k → tr> j k ) (just-injective (cong node-key eq)) (just-injective (cong node-left ( just-injective (cong node-right eq)))) x₄
                  lem11 : tr> k₁ t₁
                  lem11 = subst₂ (λ j k → tr> j k ) (just-injective (cong node-key eq)) (just-injective (cong node-right ( just-injective (cong node-right eq)))) x₅
       lem03 tree ti eq2 ti1 (r-right {kr} {vr} {t₄} {t₅} {t₆} x rt1) = lem04 t₂ _ refl (subst (λ k → treeInvariant k) eq2 ti) where
           lem04 : (t₂ tree : bt A) → tree ≡ node k₁ v₁ t₂ (node kr vr t₅ t₆) → treeInvariant tree → treeInvariant (node k₁ v₁ t₂ (node kr vr t₅ t₄))
           lem04 t₂ _ () t-leaf
           lem04 t₂ _ () (t-single key value)
           lem04 t₂ _ () (t-left key key₁ x x₁ x₂ ti)
           lem04 (node _ _ _ _) _ () (t-right key key₁ x x₁ x₂ ti1)
           lem04 leaf .(node key _ leaf (node key₁ _ _ _)) eq (t-right key key₁ x x₁ x₂ ti2) = t-right _ _ lem05 lem06 lem07 ti1 where
                  lem05 :  k₁ < kr 
                  lem05 = subst₂ (λ j k → j < k ) (just-injective (cong node-key eq)) (just-injective (cong node-key ( just-injective (cong node-right eq)))) x 
                  lem06 : tr> k₁ t₅
                  lem06 = subst₂ (λ j k → tr> j k ) (just-injective (cong node-key eq)) (just-injective (cong node-left ( just-injective (cong node-right eq)))) x₁
                  lem07 : tr> k₁ t₄
                  lem07 = <-tr> (proj2 (ti-property1 ti1)) lem05
           lem04 leaf .(node key₁ v₂ (node key v₁ t₈ t₉) (node key₂ t₇ t₁₀ t₁₁)) () (t-node key key₁ key₂ {v₁} {v₂} {t₇} {t₈} {t₉} {t₁₀} {t₁₁} x x₁ x₂ x₃ x₄ x₅ ti1 ti2)
           lem04 (node key₃ value t₂ t₃) .(node key₁ v₂ (node key v₁ t₈ t₉) (node key₂ t₇ t₁₀ t₁₁)) eq 
               (t-node key key₁ key₂ {v₁} {v₂} {t₇} {t₈} {t₉} {t₁₀} {t₁₁} x x₁ x₂ x₃ x₄ x₅ ti3 ti4) = t-node _ _ _ lem06 lem07 lem08 lem09 lem10 lem11 
                       (subst (λ k → treeInvariant k) lem05 ti3) ti1 where
                  lem05 : node key v₁ t₈ t₉ ≡ node key₃ value t₂ t₃
                  lem05 = just-injective (cong node-left eq)
                  lem06 : key₃ < k₁
                  lem06 = subst₂ (λ j k → j < k ) (just-injective (cong node-key lem05)) (just-injective (cong node-key eq)) x
                  lem07 : k₁ < kr
                  lem07 = subst₂ (λ j k → j < k ) (just-injective (cong node-key eq)) (just-injective (cong node-key ( just-injective (cong node-right eq))) ) x₁
                  lem08 : tr< k₁ t₂
                  lem08 = subst₂ (λ j k → tr< j k ) (just-injective (cong node-key eq)) (just-injective (cong node-left ( just-injective (cong node-left eq))) ) x₂
                  lem09 : tr< k₁ t₃
                  lem09 = subst₂ (λ j k → tr< j k ) (just-injective (cong node-key eq)) (just-injective (cong node-right ( just-injective (cong node-left eq))) ) x₃
                  lem10 : tr> k₁ t₅
                  lem10 = subst₂ (λ j k → tr> j k ) (just-injective (cong node-key eq)) (just-injective (cong node-left ( just-injective (cong node-right eq))) ) x₄
                  lem11 : tr> k₁ t₄
                  lem11 = <-tr> (proj2 (ti-property1 ti1)) lem07
       lem03 tree ti eq2 ti1 (r-left {kr} {vr} {t₄} {t₅} {t₆} x₃ rt1) = lem04 t₂ _ refl (subst (λ k → treeInvariant k) eq2 ti) where
           lem04 : (t₂ tree : bt A) → tree ≡ node k₁ v₁ t₂ (node kr vr t₅ t₆) → treeInvariant tree → treeInvariant (node k₁ v₁ t₂ (node kr vr t₄ t₆))
           lem04 t₂ _ () t-leaf
           lem04 t₂ _ () (t-single key value)
           lem04 t₂ _ () (t-left key key₁ x x₁ x₂ ti)
           lem04 (node _ _ _ _) _ () (t-right key key₁ x x₁ x₂ ti)
           lem04 leaf .(node key _ leaf (node key₁ _ _ _)) eq (t-right key key₁ {_} {_} {t₇} {t₈} x₀ x₁ x₂ ti) = t-right _ _ lem05 lem06 lem07 ti1 where
                  lem05 :  k₁ < kr 
                  lem05 = subst₂ (λ j k → j < k ) (just-injective (cong node-key eq)) (just-injective (cong node-key ( just-injective (cong node-right eq)))) x₀ 
                  lem08 : key ≡ k₁
                  lem08 = just-injective (cong node-key eq)
                  lem09 : t₇ ≡ t₅
                  lem09 = just-injective (cong node-left (just-injective (cong node-right eq)))
                  lem10 : t₈ ≡ t₆
                  lem10 = just-injective (cong node-right (just-injective (cong node-right eq)))
                  lem06 : tr> k₁ t₄
                  lem06 = proj1 ( proj2 ( ri-tr> _ _ _ _ _ rt x ⟪ <-trans x x₃ , ⟪ subst₂ (λ j k → tr> j k ) lem08 lem09 x₁  , subst₂ (λ j k → tr> j k ) lem08 lem10 x₂ ⟫ ⟫ )) 
                  lem07 : tr> k₁ t₆
                  lem07 = subst₂ (λ j k → tr> j k ) (just-injective (cong node-key eq)) (just-injective (cong node-right ( just-injective (cong node-right eq))) ) x₂
           lem04 leaf _ () (t-node key key₁ key₂ x x₁ x₂ x₃ x₄ x₅ ti ti₁)
           lem04 (node key₃ value t₂ t₃) .(node key₁ _ (node key _ _ _) (node key₂ _ _ _)) eq 
               (t-node key key₁ key₂ {v₁} {v₂} {t₇} {t₈} {t₉} {t₁₀} {t₁₁} x₀ x₁ x₂ x₃₃ x₄ x₅ ti ti₁) = 
                t-node _ _ _ lem06 lem07 lem08 lem09 lem10 lem11 (subst (λ k → treeInvariant k) lem05 ti) ti1 where
                  lem05 : node key v₁ t₈ t₉ ≡ node key₃ value t₂ t₃
                  lem05 = just-injective (cong node-left eq)
                  lem06 : key₃ < k₁
                  lem06 = subst₂ (λ j k → j < k ) (just-injective (cong node-key lem05)) (just-injective (cong node-key eq)) x₀
                  lem07 : k₁ < kr
                  lem07 = subst₂ (λ j k → j < k ) (just-injective (cong node-key eq)) (just-injective (cong node-key ( just-injective (cong node-right eq))) ) x₁
                  lem08 : tr< k₁ t₂
                  lem08 = subst₂ (λ j k → tr< j k ) (just-injective (cong node-key eq)) (just-injective (cong node-left ( just-injective (cong node-left eq))) ) x₂
                  lem09 : tr< k₁ t₃
                  lem09 = subst₂ (λ j k → tr< j k ) (just-injective (cong node-key eq)) (just-injective (cong node-right ( just-injective (cong node-left eq))) ) x₃₃
                  lem12 : key₁ ≡ k₁
                  lem12 = just-injective (cong node-key eq)
                  lem13 : t₁₀ ≡ t₅
                  lem13 = just-injective (cong node-left (just-injective (cong node-right eq)))
                  lem14 : t₁₁ ≡ t₆
                  lem14 = just-injective (cong node-right (just-injective (cong node-right eq)))
                  lem10 : tr> k₁ t₄
                  lem10 = proj1 ( proj2 ( ri-tr> _ _ _ _ _ rt x ⟪ <-trans x x₃ , ⟪ subst₂ (λ j k → tr> j k ) lem12 lem13 x₄  , subst₂ (λ j k → tr> j k ) lem12 lem14 x₅ ⟫ ⟫ )) 
                  lem11 : tr> k₁ t₆
                  lem11 = <-tr> (proj2 (ti-property1 ti1)) lem07
   lem00 tree .(node _ _ _ _) key value eq1 ti (r-left  {k₁} {v₁} {t₁} {t₂} {t₃} x rt) = lem03 _ ti eq1 lem02 rt where
       lem01 : treeInvariant t₂
       lem01 = treeLeftDown _ _ (subst (λ k → treeInvariant k ) eq1 ti )
       lem02 : treeInvariant t₁
       lem02 = RTtoTI0 _ t₁ key value lem01 rt
       lem03 : (tree : bt A) → treeInvariant tree → tree ≡ node k₁ v₁ t₂ t₃  → treeInvariant t₁ 
            → replacedTree _ _ t₂ t₁ →  treeInvariant (node k₁ v₁ t₁ t₃)
       lem03 tree ti eq2 ti1 r-leaf = lem04 _ refl (subst (λ k → treeInvariant k) eq2 ti) where
           lem04 : (tree : bt A) → tree ≡ node k₁ v₁ leaf t₃ → treeInvariant tree → treeInvariant (node k₁ v₁ (node key value leaf leaf) t₃)
           lem04 _ () t-leaf
           lem04 _ eq (t-single key value) = subst (λ k → treeInvariant (node k₁ v₁ (node _ _ leaf leaf) k)) 
               (just-injective (cong node-right eq) ) (t-left _ _ x _ _ (t-single _ _) )
           lem04 _ eq (t-left key key₁ {_} {_} {t₄} {t₅} x₀ x₁ x₂ ti) = subst (λ k → treeInvariant (node k₁ v₁ (node _ _ leaf leaf) k)) 
               (just-injective (cong node-right eq) ) (t-left _ _ x _ _ (t-single _ _) )
           lem04  _ eq (t-right key key₁ {_} {_} {t₄} {t₅} x₀ x₁ x₂ ti) = subst (λ k → treeInvariant (node k₁ v₁ (node _ _ leaf leaf) k)) 
              (just-injective (cong node-right eq) ) ( t-node _ _ _ x (subst (λ j → j < key₁ ) lem05 x₀)  tt tt (subst (λ j → tr> j t₄) lem05 x₁) 
                (subst (λ j → tr> j t₅) lem05 x₂)  (t-single _ _ ) ti) where
                  lem05 : key  ≡ k₁
                  lem05 = just-injective (cong node-key eq)
           lem04 _ () (t-node key key₁ key₂ x₁ x₂ x₃ x₄ x₅ x₆ ti ti₁)
       lem03 tree ti eq2 ti1 (r-node {value₁} {t} {t₁}) = lem04 _ refl (subst (λ k → treeInvariant k) eq2 ti) where
           lem04 : (tree : bt A) → tree ≡ node k₁ v₁ (node key value₁ t t₁) t₃ → treeInvariant tree → treeInvariant (node k₁ v₁ (node  key value t t₁) t₃)
           lem04 .leaf () t-leaf
           lem04 .(node key value leaf leaf) () (t-single key value)
           lem04 .(node key value₂ leaf (node key₁ _ t₄ t₅)) () (t-right key key₁ {value₂} {_} {t₄} {t₅} x x₁ x₂ ti)
           lem04 _ eq (t-left key key₁ {value₂} {_} {t₄} {t₅} x₀ x₁ x₂ ti) = subst (λ k → treeInvariant (node k₁ v₁ (node _ _ t t₁) k))  
               (just-injective (cong node-right eq) ) (t-left _ _ x (subst₂ (λ j k → tr< j k ) lem05 lem06 x₁)  (subst₂ (λ j k → tr< j k ) lem05 lem07 x₂) ti1 ) where
                  lem05 : key₁ ≡ k₁
                  lem05 = just-injective (cong node-key eq)
                  lem06 : t₄ ≡ t
                  lem06 = just-injective (cong node-left (just-injective (cong node-left eq)))
                  lem07 : t₅ ≡ t₁
                  lem07 = just-injective (cong node-right (just-injective (cong node-left eq)))
           lem04 .(node key₁ _ (node key _ _ _) (node key₂ _ _ _)) eq (t-node key key₁ key₂ {v₁} {v₂} {t₇} {t₈} {t₉} {t₁₀} {t₁₁} x₀ x₁ x₂ x₃ x₄ x₅ ti ti₁) 
             = subst (λ k → treeInvariant (node k₁ _ (node _ _ t t₁) k)) (just-injective (cong node-right eq) ) 
                (t-node _ _ _ x (subst (λ j → j < key₂) lem05 x₁)  lem06 lem07 lem08 lem09 ti1 ti₁) where
                  lem05 : key₁ ≡ k₁
                  lem05 = just-injective (cong node-key eq)
                  lem06 : tr< k₁ t
                  lem06 = subst₂ (λ j k → tr< j k) lem05 (just-injective (cong node-left ( just-injective (cong node-left eq )))) x₂
                  lem07 : tr< k₁ t₁
                  lem07 = subst₂ (λ j k → tr< j k) lem05 (just-injective (cong node-right ( just-injective (cong node-left eq )))) x₃
                  lem08 : tr> k₁ t₁₀
                  lem08 = subst (λ j  → tr> j _) lem05 x₄
                  lem09 : tr> k₁ t₁₁
                  lem09 = subst (λ j  → tr> j _) lem05 x₅
       lem03 tree ti eq2 ti1 (r-right {kr} {vr} {t₄} {t₅} {t₆} x₃ rt2) = lem04 _ _ refl (subst (λ k → treeInvariant k) eq2 ti) where
           lem04 : (t₃ tree : bt A) → tree ≡  node k₁ v₁ (node kr vr t₅ t₆) t₃ → treeInvariant tree → treeInvariant (node k₁ v₁ (node kr vr t₅ t₄) t₃) 
           lem04 t₃ _ () t-leaf
           lem04 t₃ _ () (t-single key value)
           lem04 t₃ _ eq (t-left key key₁ {value₂} {_} {t₆} {t₇} x₀ x₁ x₂ ti) = subst (λ k → treeInvariant (node k₁ v₁ (node kr vr t₅ t₄) k))
               (just-injective (cong node-right eq) ) (t-left _ _ (subst₂ (λ j k → j < k ) lem06 lem05 x₀)  lem07 lem08 ti1) where
                  lem05 : key₁ ≡ k₁
                  lem05 = just-injective (cong node-key eq)
                  lem06 : key ≡ kr
                  lem06 = just-injective (cong node-key ( just-injective (cong node-left eq)))
                  lem07 : tr< k₁ t₅
                  lem07 = subst₂ (λ j k → tr< j k ) lem05 (just-injective (cong node-left (just-injective (cong node-left eq))) ) x₁
                  lem08 : tr< k₁ t₄
                  lem08 = ri-tr< _ _ _ _ _ rt2 x (subst₂ (λ j k → tr< j k ) lem05 (just-injective (cong node-right (just-injective (cong node-left eq)))) x₂)
           lem04 (node _ _ _ _) _ () (t-right key key₁ x x₁ x₂ ti1)
           lem04 leaf .(node key _ leaf (node key₁ _ _ _)) () (t-right key key₁ x x₁ x₂ ti2)
           lem04 leaf .(node key₁ v₂ (node key v₁ t₈ t₉) (node key₂ t₇ t₁₀ t₁₁)) () (t-node key key₁ key₂ {v₁} {v₂} {t₇} {t₈} {t₉} {t₁₀} {t₁₁} x x₁ x₂ x₃ x₄ x₅ ti1 ti2)
           lem04 (node key₃ value t₂ t₃) .(node key₁ v₂ (node key v₁ t₈ t₉) (node key₂ v₃ t₁₀ t₁₁)) eq 
               (t-node key key₁ key₂ {v₁} {v₂} {v₃} {t₈} {t₉} {t₁₀} {t₁₁} x₀ x₁ x₂ x₃₃ x₄ x₅ ti3 ti4) 
                 = t-node _ _ _ (<-trans x₃ x )  lem06 lem07 lem08 lem09 lem10 ti1 (subst (λ k → treeInvariant k) lem05 ti4) where
                  lem05 : node key₂ v₃ t₁₀ t₁₁ ≡ node key₃ value t₂ t₃
                  lem05 = just-injective (cong node-right eq)
                  lem06 : k₁ < key₃ 
                  lem06 = subst₂ (λ j k → j < k ) (just-injective (cong node-key eq)) (just-injective (cong node-key ( just-injective (cong node-right eq))) ) x₁
                  lem18 : key₁ ≡ k₁
                  lem18 = just-injective (cong node-key eq)
                  lem07 : tr< k₁ t₅
                  lem07 = subst₂ (λ j k → tr< j k ) lem18 (just-injective (cong node-left ( just-injective (cong node-left eq))) ) x₂
                  lem08 : tr< k₁ t₄
                  lem08 = ri-tr< _ _ _ _ _ rt2 x (subst₂ (λ j k → tr< j k ) lem18 (just-injective (cong node-right ( just-injective (cong node-left eq))) ) x₃₃ )
                  lem09 : tr> k₁ t₂
                  lem09 = subst₂ (λ j k → tr> j k ) lem18 (just-injective (cong node-left ( just-injective (cong node-right eq))) ) x₄ 
                  lem10 : tr> k₁ t₃ 
                  lem10 = subst₂ (λ j k → tr> j k ) lem18 (just-injective (cong node-right ( just-injective (cong node-right eq))) ) x₅ 
       lem03 tree ti eq2 ti1 (r-left {kr} {vr} {t₄} {t₅} {t₆} x₃ rt1) = lem04 t₃ _ refl (subst (λ k → treeInvariant k) eq2 ti) where
           lem04 : (t₃ tree : bt A) → tree ≡ node k₁ v₁ (node kr vr t₅ t₆) t₃ → treeInvariant tree → treeInvariant (node k₁ v₁ (node kr vr t₄ t₆) t₃)
           lem04 t₃ _ () t-leaf
           lem04 t₃ _ () (t-single key value)
           lem04 t₃ _ () (t-right key key₁ x x₁ x₂ ti) 
           lem04 (node key₃ value t₂ t₃) _ () (t-left key key₁ {_} {_} {t₇} {t₈} x₀ x₁ x₂ ti)
           lem04 leaf _ eq (t-left key key₁ {_} {_} {t₇} {t₈} x₀ x₁ x₂ ti) = t-left _ _ lem05 lem06 lem07 ti1 where
                  lem08 : key₁ ≡ k₁
                  lem08 = just-injective (cong node-key eq)
                  lem05 : kr < k₁  
                  lem05 = subst₂ (λ j k → j < k ) (just-injective (cong node-key ( just-injective (cong node-left eq))) ) lem08 x₀
                  lem06 : tr< k₁ t₄
                  lem06 = ri-tr< _ _ _ _ _ rt1 x (subst₂ (λ j k → tr< j k ) lem08 (just-injective (cong node-left ( just-injective (cong node-left eq))) ) x₁)
                  lem07 : tr< k₁ t₆
                  lem07 = subst₂ (λ j k → tr< j k ) lem08 (just-injective (cong node-right ( just-injective (cong node-left eq))) ) x₂
           lem04 leaf _ () (t-node key key₁ key₂ x x₁ x₂ x₃ x₄ x₅ ti ti₁)
           lem04 (node key₃ value t₂ t₃) .(node key₁ _ (node key _ _ _) (node key₂ _ _ _)) eq 
              (t-node key key₁ key₂ {v₁} {v₂} {v₃} {t₈} {t₉} {t₁₀} {t₁₁} x₀ x₁ x₂ x₃ x₄ x₅ ti ti₁) = t-node _ _ _ lem05 lem06 lem07 lem09 lem10 lem11 
                       ti1 (subst (λ k → treeInvariant k) (just-injective (cong node-right eq)) ti₁) where
                  lem08 : key₁ ≡ k₁
                  lem08 = just-injective (cong node-key eq)
                  lem05 : kr < k₁  
                  lem05 = subst₂ (λ j k → j < k ) (just-injective (cong node-key ( just-injective (cong node-left eq))) ) lem08 x₀
                  lem06 : k₁ < key₃
                  lem06 = subst₂ (λ j k → j < k ) (just-injective (cong node-key eq)) (just-injective (cong node-key ( just-injective (cong node-right eq))) ) x₁
                  lem07 : tr< k₁ t₄
                  lem07 = ri-tr< _ _ _ _ _ rt1 x (subst₂ (λ j k → tr< j k ) lem08 (just-injective (cong node-left ( just-injective (cong node-left eq))) ) x₂)
                  lem09 : tr< k₁ t₆
                  lem09 = subst₂ (λ j k → tr< j k ) lem08 (just-injective (cong node-right ( just-injective (cong node-left eq))) ) x₃
                  lem10 : tr> k₁ t₂
                  lem10 = subst₂ (λ j k → tr> j k ) (just-injective (cong node-key eq)) (just-injective (cong node-left ( just-injective (cong node-right eq))) ) x₄
                  lem11 : tr> k₁ t₃
                  lem11 = subst₂ (λ j k → tr> j k ) (just-injective (cong node-key eq)) (just-injective (cong node-right ( just-injective (cong node-right eq))) ) x₅

si-property3 : {n : Level} {A : Set n} → (stack rest : List ( bt A))
           → ( tree orig : bt A) →  (key : ℕ)
           → stack ≡ ( tree ∷ leaf ∷ rest )
           → ¬ stackInvariant key tree  orig stack
si-property3 {n} {A} stack rest tree orig key eq si = lem00 stack si eq where
    lem00 :  (stack : List (bt A)) → stackInvariant key tree  orig stack → stack ≡ (tree ∷ leaf ∷ rest ) → ⊥
    lem00 _ s-nil ()
    lem00 _ (s-right .tree .orig tree₁ x si1) eq with si-property1 (subst₂ (λ j k → stackInvariant key j orig k) refl (∷-injectiveʳ eq)  si1)
    ... | ()
    lem00 _ (s-left tree₁ .orig tree x si1) eq with si-property1 (subst₂ (λ j k → stackInvariant key j orig k) refl (∷-injectiveʳ eq)  si1)
    ... | ()

popStackInvariant : {n : Level} {A : Set n} → (rest : List ( bt A))
           → ( tree parent orig : bt A) →  (key : ℕ)
           → stackInvariant key tree  orig ( tree ∷ parent ∷ rest )
           → stackInvariant key parent orig (parent ∷ rest )
popStackInvariant {n} {A} rest tree parent orig key si = lem00 _ ( tree ∷ parent ∷ rest ) si refl where
    lem00 : (parent : bt A) → (stack : List (bt A)) → stackInvariant key tree  orig stack → stack ≡ (tree ∷ parent ∷ rest ) → stackInvariant key parent orig (parent ∷ rest )
    lem00 leaf _ si1 eq = ⊥-elim (si-property3 _ _ _ _ _ eq si1)
    lem00 (node pkey pvalue left right) .(tree ∷ _) (s-right .tree .orig tree₁ x si1) eq
       = subst₂ (λ j k → stackInvariant key j orig k ) (sym (si-property1 (subst₂ (λ j k → stackInvariant key j orig k)
            refl (∷-injectiveʳ eq) si1)))  (∷-injectiveʳ eq) si1
    lem00 (node pkey pvalue left right) (tree₁ ∷ _) (s-left .tree₁ .orig tree x si1) eq
       = subst₂ (λ j k → stackInvariant key j orig k ) (sym (si-property1 (subst₂ (λ j k → stackInvariant key j orig k)
            refl (∷-injectiveʳ eq) si1)))  (∷-injectiveʳ eq) si1

siToTreeinvariant : {n : Level} {A : Set n} → (rest : List ( bt A))
           → ( tree orig : bt A) →  (key : ℕ)
           → treeInvariant orig
           → stackInvariant key tree  orig ( tree ∷ rest )
           → treeInvariant tree
siToTreeinvariant {n} {A} rest tree orig key ti si = lem00 _ (tree ∷ rest) rest si refl ti where
    lem00 : (tree : bt A) → (stack rest : List (bt A)) → stackInvariant key tree  orig stack → stack ≡ (tree ∷ rest ) → treeInvariant orig → treeInvariant tree
    lem00 _ (tree ∷ []) _ (s-right .tree .orig tree₁ {key₁} {v₁}  x si1) eq tio = ⊥-elim (si-property0 si1 refl)
    lem00 _ (tree ∷ leaf ∷ st) _ (s-right .tree .orig tree₁ {key₁} {v₁} x si1) eq tio with si-property1 si1
    ... | ()
    lem00 _ st0@(tree ∷ parent @ (node key₁ value tree₃ tree₁) ∷ st) rest₀ si2@(s-right .tree .orig tree₂ {key₂} {v₁} x si1) eq tio =
       treeRightDown _ _ (lem01 _ st0 si2 (cong (λ k → tree ∷ node key₁ value tree₃ k ∷ st) lem02 ))  where
          lem02 : tree₁ ≡ tree
          lem02 = just-injective (cong node-right (si-property1 si1))
          lem01 : (parent : bt A) → (stack : List (bt A)) → stackInvariant key tree  orig stack → stack ≡ (tree ∷ parent ∷ st ) → treeInvariant parent
          lem01 parent .(orig ∷ []) s-nil ()
          lem01 parent (tree ∷ []) (s-right .tree .orig tree₁ {key₃} {v₃} x si) ()
          lem01 parent (tree ∷ parent₁ ∷ st3) (s-right .tree .orig tree₁ {key₃} {v₃} x si) eq3 = subst (λ k → treeInvariant k) lem03 (lem00 _ _ st si lem04 tio) where
             lem03 : node key₃ v₃ tree₁ tree ≡ parent
             lem03 = trans (sym (si-property1 si)) (∷-injectiveˡ (∷-injectiveʳ eq3))
             lem04 : parent₁ ∷ st3 ≡ node key₃ v₃ tree₁ tree ∷ st
             lem04 = cong₂ (λ j k → j ∷ k) (si-property1 si) (∷-injectiveʳ (∷-injectiveʳ eq3))
          lem01 parent (tree ∷ []) (s-left .tree .orig tree₁ {key₃} {v₃} x si) ()
          lem01 parent (tree ∷ parent₁ ∷ st3) (s-left .tree .orig tree₁ {key₃} {v₃} x si) eq3 = subst (λ k → treeInvariant k) lem03 (lem00 _ _ st si lem04 tio) where
             lem03 :  node key₃ v₃ tree tree₁ ≡ parent
             lem03 = trans (sym (si-property1 si)) (∷-injectiveˡ (∷-injectiveʳ eq3))
             lem04 : parent₁ ∷ st3 ≡ node key₃ v₃ tree tree₁ ∷ st
             lem04 = cong₂ (λ j k → j ∷ k) (si-property1 si) (∷-injectiveʳ (∷-injectiveʳ eq3))
    lem00 _ (tree ∷ []) _ (s-left .tree .orig tree₁ {key₁} {v₁}  x si1) eq tio = ⊥-elim (si-property0 si1 refl)
    lem00 _ (tree ∷ leaf ∷ st) _ (s-left .tree .orig tree₁ {key₁} {v₁} x si1) eq tio with si-property1 si1
    ... | ()
    lem00 _ st0@(tree ∷ parent @ (node key₁ value tree₃ tree₁) ∷ st) rest₀ si2@(s-left .tree .orig tree₂ {key₂} {v₁} x si1) eq tio =
       treeLeftDown _ _ (lem01 _ st0 si2 (cong (λ k → tree ∷ node key₁ value k tree₁ ∷ st) lem02 ))  where
          lem02 : tree₃ ≡ tree
          lem02 = just-injective (cong node-left (si-property1 si1))
          lem01 : (parent : bt A) → (stack : List (bt A)) → stackInvariant key tree  orig stack → stack ≡ (tree ∷ parent ∷ st ) → treeInvariant parent
          lem01 parent .(orig ∷ []) s-nil ()
          lem01 parent (tree ∷ []) (s-right .tree .orig tree₁ {key₃} {v₃} x si) ()
          lem01 parent (tree ∷ parent₁ ∷ st3) (s-right .tree .orig tree₁ {key₃} {v₃} x si) eq3 = subst (λ k → treeInvariant k) lem03 (lem00 _ _ st si lem04 tio) where
             lem03 : node key₃ v₃ tree₁ tree ≡ parent
             lem03 = trans (sym (si-property1 si)) (∷-injectiveˡ (∷-injectiveʳ eq3))
             lem04 : parent₁ ∷ st3 ≡ node key₃ v₃ tree₁ tree ∷ st
             lem04 = cong₂ (λ j k → j ∷ k) (si-property1 si) (∷-injectiveʳ (∷-injectiveʳ eq3))
          lem01 parent (tree ∷ []) (s-left .tree .orig tree₁ {key₃} {v₃} x si) ()
          lem01 parent (tree ∷ parent₁ ∷ st3) (s-left .tree .orig tree₁ {key₃} {v₃} x si) eq3 = subst (λ k → treeInvariant k) lem03 (lem00 _ _ st si lem04 tio) where
             lem03 : node key₃ v₃ tree tree₁ ≡ parent
             lem03 = trans (sym (si-property1 si)) (∷-injectiveˡ (∷-injectiveʳ eq3))
             lem04 : parent₁ ∷ st3 ≡ node key₃ v₃ tree tree₁ ∷ st
             lem04 = cong₂ (λ j k → j ∷ k) (si-property1 si) (∷-injectiveʳ (∷-injectiveʳ eq3))
    lem00 _ _ _ s-nil eq tio = tio

child-repaced-ti : {n : Level} {A : Set n} (key : ℕ) (tree : bt A) → treeInvariant tree → treeInvariant (child-replaced key tree)
child-repaced-ti {n} {A} key tree ti =  ch00 tree _ ti refl where
     ch00 : (tree tree₁ : bt A) → treeInvariant tree  → tree₁ ≡ child-replaced key tree → treeInvariant tree₁
     ch00 leaf tree₁ ti eq = subst (λ k → treeInvariant k) (sym eq) t-leaf
     ch00 (node key₁ value tree tree₂) tree₁ ti₁ eq with <-cmp key key₁
     ... | tri< a ¬b ¬c = subst (λ k → treeInvariant k) (sym eq) (treeLeftDown _ _ ti₁ )
     ... | tri≈ ¬a b ¬c = subst (λ k → treeInvariant k) (sym eq) ti₁
     ... | tri> ¬a ¬b c = subst (λ k → treeInvariant k) (sym eq) (treeRightDown _ _ ti₁ )


record replacePR {n : Level} {A : Set n} (key : ℕ) (value : A) (tree repl : bt A ) (stack : List (bt A)) (C : bt A → bt A → List (bt A) → Set n) : Set n where
   field
     tree0 : bt A
     ti : treeInvariant tree0
     si : stackInvariant key tree tree0 stack
     ri : replacedTree key value (child-replaced key tree ) repl
     rti : treeInvariant repl
     ci : C tree repl stack     -- data continuation

replaceNodeP : {n m : Level} {A : Set n} {t : Set m} → (key : ℕ) → (value : A) → (tree : bt A)
    → (tree ≡ leaf ) ∨ ( node-key tree ≡ just key )
    → (treeInvariant tree ) → ((tree1 : bt A) → treeInvariant tree1 →  replacedTree key value (child-replaced key tree) tree1 → t) → t
replaceNodeP k v1 leaf C P next = next (node k v1 leaf leaf) (t-single k v1 ) r-leaf
replaceNodeP k v1 (node k₁ value t t₁) (case1 ()) P next
replaceNodeP k v1 (node k₁ value t t₁) (case2 eq) P next = next (node k v1 t t₁) (replaceTree1 k value v1 (subst (λ k → treeInvariant (node k value t t₁)) repl01 P)) repl00 where
         repl01 : k₁ ≡ k
         repl01 = just-injective eq
         repl00 :  replacedTree k v1 (child-replaced k (node k₁ value t t₁)) (node k v1 t t₁) 
         repl00 = subst (λ j → replacedTree k v1 j (node k v1 t t₁)) (trans (cong (λ k → node k value t t₁) (sym repl01) )  (sym ( child-replaced-eq repl01 )) ) r-node

replaceP : {n m : Level} {A : Set n} {t : Set m}
     → (key : ℕ) → (value : A) → {tree : bt A} ( repl : bt A)
     → (stack : List (bt A)) → replacePR key value tree repl stack (λ _ _ _ → Lift n ⊤)
     → (next : ℕ → A → {tree1 : bt A } (repl : bt A) → (stack1 : List (bt A))
         → replacePR key value tree1 repl stack1 (λ _ _ _ → Lift n ⊤) → length stack1 < length stack → t)
     → (exit : (tree1 repl : bt A) → treeInvariant repl ∧ replacedTree key value tree1 repl → t) → t
replaceP key value {tree}  repl [] Pre next exit = ⊥-elim ( si-property0 (replacePR.si Pre) refl ) -- can't happen
replaceP key value {tree}  repl (leaf ∷ []) Pre next exit  =  exit (replacePR.tree0 Pre) (node key value leaf leaf) ⟪ t-single _ _  ,  repl00 ⟫ where
    repl00 : replacedTree key value (replacePR.tree0 Pre) (node key value leaf leaf)
    repl00 = subst (λ k → replacedTree key value k (node key value leaf leaf)) (just-injective (si-property-last  _ _ _ _  (replacePR.si Pre))) r-leaf
replaceP key value {tree}  repl (node key₁ value₁ left right ∷ []) Pre next exit with <-cmp key key₁
... | tri< a ¬b ¬c = exit (replacePR.tree0 Pre) (node key₁ value₁ repl right ) ⟪ RTtoTI0 _ _ _ _ (replacePR.ti Pre) repl02 , repl02 ⟫ where
     repl03 : node key₁ value₁ (child-replaced key tree) right ≡ replacePR.tree0 Pre
     repl03 = begin
         node key₁ value₁ (child-replaced key tree) right ≡⟨ cong (λ k → node key₁ value₁ (child-replaced key k) right) (sym (si-property1 (replacePR.si Pre ))) ⟩
         node key₁ value₁ (child-replaced key (node key₁ value₁ left right)) right ≡⟨ cong  (λ k → node key₁ value₁ k right ) (child-replaced-left a ) ⟩
         node key₁ value₁ left right ≡⟨ just-injective (si-property-last  _ _ _ _  (replacePR.si Pre)) ⟩
         replacePR.tree0 Pre ∎ where 
            open ≡-Reasoning
     repl02 : replacedTree key value (replacePR.tree0 Pre) (node key₁ value₁ repl right)
     repl02 = subst (λ k → replacedTree key value k (node key₁ value₁ repl right) ) repl03 ( r-left a (replacePR.ri Pre))
... | tri≈ ¬a b ¬c = exit (replacePR.tree0 Pre) repl ⟪  RTtoTI0 _ _ _ _ (replacePR.ti Pre) repl02 , repl02 ⟫ where
    repl03 : child-replaced key tree ≡ replacePR.tree0 Pre
    repl03 = begin
        child-replaced key tree ≡⟨ cong (λ k → child-replaced key k ) (sym (si-property1 (replacePR.si Pre))) ⟩
        child-replaced key (node key₁ value₁ left right) ≡⟨ child-replaced-eq (sym b) ⟩
        node key₁ value₁ left right ≡⟨ just-injective (si-property-last  _ _ _ _  (replacePR.si Pre)) ⟩
        replacePR.tree0 Pre ∎ where open ≡-Reasoning
    repl02 : replacedTree key value (replacePR.tree0 Pre) repl
    repl02 = subst (λ k → replacedTree key value k repl ) repl03 (replacePR.ri Pre) 
... | tri> ¬a ¬b c = exit (replacePR.tree0 Pre) (node key₁ value₁ left repl  ) ⟪  RTtoTI0 _ _ _ _ (replacePR.ti Pre) repl02 , repl02 ⟫ where
     repl03 : node key₁ value₁ left (child-replaced key tree) ≡ replacePR.tree0 Pre
     repl03 = begin
         node key₁ value₁ left (child-replaced key tree) ≡⟨ cong (λ k → node key₁ value₁ left (child-replaced key k) ) (sym (si-property1 (replacePR.si Pre ))) ⟩
         node key₁ value₁ left (child-replaced key (node key₁ value₁ left right)) ≡⟨ cong  (λ k → node key₁ value₁ left k ) (child-replaced-right c ) ⟩
         node key₁ value₁ left right ≡⟨ just-injective (si-property-last  _ _ _ _  (replacePR.si Pre)) ⟩
         replacePR.tree0 Pre ∎ where 
            open ≡-Reasoning
     repl02 : replacedTree key value (replacePR.tree0 Pre) (node key₁ value₁ left repl )
     repl02 = subst (λ k → replacedTree key value k (node key₁ value₁ left repl )  ) repl03 ( r-right c (replacePR.ri Pre))
replaceP {n} {_} {A} key value  {tree}  repl (leaf ∷ st@(tree1 ∷ st1)) Pre next exit = next key value repl st Post ≤-refl where
    Post :  replacePR key value tree1 repl (tree1 ∷ st1) (λ _ _ _ → Lift n ⊤)
    Post = record { tree0 = replacePR.tree0 Pre ; ti = replacePR.ti Pre ; si = repl10 ; ri = repl12 _ (replacePR.si Pre) refl ;  rti = replacePR.rti Pre ; ci = lift tt } where
         repl10 : stackInvariant key tree1 (replacePR.tree0 Pre) (tree1 ∷ st1)
         repl10 = popStackInvariant _ _ _ _ _  (subst (λ k → stackInvariant  key k (replacePR.tree0 Pre) (leaf ∷ tree1 ∷ st1) ) 
             (sym (si-property1 (replacePR.si Pre)))  (replacePR.si Pre) )
         repl12 : (stack : List (bt A)) → stackInvariant key tree (replacePR.tree0 Pre) stack → stack ≡ (leaf ∷ tree1 ∷ st1) 
             → replacedTree key value (child-replaced key  tree1  ) repl
         repl12 _ s-nil ()
         repl12 (node k₁ v₁ left right ∷ st₁) (s-right .(node k₁ v₁ left right) .(replacePR.tree0 Pre) tree₁ x si) ()
         repl12 (leaf ∷ st₁) (s-right .tree .(replacePR.tree0 Pre) tree₁ {key₁} {v₁} x si) eq = subst₂ (λ j k → replacedTree key value j k ) lem10 lem09 r-leaf where
            lem09 : node key value leaf leaf ≡ repl
            lem09 = sym (rt-property-leaf (replacePR.ri Pre))
            lem10 : leaf ≡ child-replaced key tree1
            lem10 = begin
                leaf ≡⟨ sym (child-replaced-right x ) ⟩
                child-replaced key (node key₁ _ tree₁ leaf)  ≡⟨ cong (child-replaced key) (sym repl13) ⟩
                child-replaced key tree1 ∎ where 
                  open ≡-Reasoning
                  repl13 : tree1 ≡ node key₁ v₁ tree₁ leaf 
                  repl13 = si-property1 (subst (λ k → stackInvariant key (node key₁ v₁ tree₁ leaf) (replacePR.tree0 Pre) k) (∷-injectiveʳ eq) si )
         repl12 (node k₁ v₁ left right ∷ st₁) (s-left .(node k₁ v₁ left right) .(replacePR.tree0 Pre) tree₁ x si) ()
         repl12 (leaf ∷ st₁) (s-left .tree .(replacePR.tree0 Pre) tree₁ {key₁} {v₁} x si) eq = subst₂ (λ j k → replacedTree key value j k ) lem10 lem09 r-leaf where
            lem09 : node key value leaf leaf ≡ repl
            lem09 = sym (rt-property-leaf (replacePR.ri Pre))
            lem10 : leaf ≡ child-replaced key tree1
            lem10 = begin
                leaf ≡⟨ sym (child-replaced-left x ) ⟩
                child-replaced key (node key₁ _ leaf tree₁ )  ≡⟨ cong (child-replaced key) (sym repl13) ⟩
                child-replaced key tree1 ∎ where 
                  open ≡-Reasoning
                  repl13 : tree1 ≡ node key₁ v₁ leaf tree₁ 
                  repl13 = si-property1 (subst (λ k → stackInvariant key (node key₁ v₁ leaf tree₁ ) (replacePR.tree0 Pre) k) (∷-injectiveʳ eq) si )
replaceP {n} {_} {A} key value {tree}  repl (nd@( node key₁ value₁ left right) ∷ st@(tree1 ∷ st1)) Pre next exit  with <-cmp key key₁
... | tri< a ¬b ¬c = next key value (node key₁ value₁ repl right ) st Post ≤-refl where
    Post : replacePR key value tree1 (node key₁ value₁ repl right ) st (λ _ _ _ → Lift n ⊤)
    Post = record { tree0 = replacePR.tree0 Pre ; ti = replacePR.ti Pre ; si = repl10 ; ri = repl12 _ (replacePR.si Pre) refl ;  rti = lem14 ; ci = lift tt } where
         repl10 : stackInvariant key tree1 (replacePR.tree0 Pre) (tree1 ∷ st1)
         repl10 = popStackInvariant _ _ _ _ _  (subst (λ k → stackInvariant  key k (replacePR.tree0 Pre) (nd ∷ tree1 ∷ st1) ) 
             (sym (si-property1 (replacePR.si Pre)))  (replacePR.si Pre) )
         repl12 : (stack : List (bt A)) → stackInvariant key tree (replacePR.tree0 Pre) stack → stack ≡ (nd ∷ tree1 ∷ st1) 
             → replacedTree key value (child-replaced key tree1) (node key₁ value₁ repl right)
         repl12 _ s-nil ()
         repl12 (leaf ∷ st₁) (s-right .leaf .(replacePR.tree0 Pre) tree₁ {key₂} {v₂} x si) ()
         repl12 (node k₁ v₁ left₂ right₂ ∷ st₁) (s-right .(node k₁ v₁ left₂ right₂) .(replacePR.tree0 Pre) tree₁  {key₂} {v₂} x si) eq = lem13 where
          --   si     : stackInvariant key (node key₂ v₂ tree₁ (node k₁ v₁ left₂ right₂)) (replacePR.tree0 Pre) st₁
          --   eq     : node k₁ v₁ left₂ right₂ ∷ st₁ ≡ node key₁ value₁ left right ∷ tree1 ∷ st1
            lem20 : node k₁ v₁ left₂ right₂ ≡ node key₁ value₁ left right 
            lem20 = ∷-injectiveˡ eq
            lem21 : tree1 ≡ node key₂ v₂ tree₁ (node k₁ v₁ left₂ right₂)
            lem21 = (si-property1 (subst₂ (λ j k →  stackInvariant key _ j  k ) refl (∷-injectiveʳ eq) si ))
            lem10 : node key₁ value₁ (child-replaced key (node k₁ v₁ left₂ right₂)) right  ≡ child-replaced key tree1
            lem10 = begin
                node key₁ value₁ (child-replaced key (node k₁ v₁ left₂ right₂)) right  ≡⟨ cong ( λ k → node key₁ value₁ k right ) ( child-replaced-left repl13 ) ⟩
                node key₁ value₁ left₂ right  ≡⟨ cong ( λ k → node key₁ value₁ k right ) (just-injective (cong node-left lem20)) ⟩
                node key₁ value₁ left right  ≡⟨ sym lem20 ⟩ 
                node k₁ v₁ left₂ right₂ ≡⟨ sym ( child-replaced-right x) ⟩
                child-replaced key (node key₂ v₂ tree₁ (node k₁ v₁ left₂ right₂)) ≡⟨ sym ( cong (child-replaced key ) lem21 ) ⟩ 
                child-replaced key tree1 ∎ where 
                  open ≡-Reasoning
                  repl13 : key < k₁
                  repl13 = subst (λ k → key < k) (sym (just-injective (cong node-key lem20))) a
            lem13 : replacedTree key value (child-replaced key tree1) (node key₁ value₁ repl right )
            lem13 = subst (λ k → replacedTree key value k (node key₁ value₁ repl right) ) lem10  (r-left a (replacePR.ri Pre))
         repl12 (leaf ∷ st₁) (s-left .tree .(replacePR.tree0 Pre) tree₁ {key₂} {v₂} x si) ()
         repl12 (node k₁ v₁ left₂ right₂ ∷ st₁) (s-left .(node k₁ v₁ left₂ right₂) .(replacePR.tree0 Pre) tree₁ {key₂} {v₂} x si) eq = lem13 where
            lem20 : node k₁ v₁ left₂ right₂ ≡ node key₁ value₁ left right 
            lem20 = ∷-injectiveˡ eq
            lem21 : tree1 ≡ node key₂ v₂ (node k₁ v₁ left₂ right₂) tree₁
            lem21 = (si-property1 (subst₂ (λ j k →  stackInvariant key _ j  k ) refl (∷-injectiveʳ eq) si ))
            lem10 : node key₁ value₁ (child-replaced key (node k₁ v₁ left₂ right₂)) right  ≡ child-replaced key tree1
            lem10 = begin
                node key₁ value₁ (child-replaced key (node k₁ v₁ left₂ right₂)) right  ≡⟨ cong ( λ k → node key₁ value₁ k right ) ( child-replaced-left repl13 ) ⟩
                node key₁ value₁ left₂ right  ≡⟨ cong ( λ k → node key₁ value₁ k right ) (just-injective (cong node-left lem20)) ⟩
                node key₁ value₁ left right  ≡⟨ sym lem20 ⟩ 
                node k₁ v₁ left₂ right₂ ≡⟨ sym ( child-replaced-left x) ⟩
                child-replaced key (node key₂ v₂ (node k₁ v₁ left₂ right₂) tree₁ ) ≡⟨ sym ( cong (child-replaced key ) lem21 ) ⟩ 
                child-replaced key tree1 ∎ where 
                  open ≡-Reasoning
                  repl13 : key < k₁
                  repl13 = subst (λ k → key < k) (sym (just-injective (cong node-key lem20))) a
            lem13 : replacedTree key value (child-replaced key tree1) (node key₁ value₁ repl right )
            lem13 = subst (λ k → replacedTree key value k (node key₁ value₁ repl right) ) lem10  (r-left a (replacePR.ri Pre))
         lem14 : treeInvariant (node key₁ value₁ repl right)
         lem14 = RTtoTI0 _ _ _ _ (child-repaced-ti key tree1 (siToTreeinvariant _ tree1 _ _ (replacePR.ti Pre) repl10 )) (repl12 _ (replacePR.si Pre) refl)
... | tri≈ ¬a b ¬c = next key value (node key₁ value  left right ) st Post ≤-refl where
    Post :  replacePR key value tree1 (node key₁ value left right ) (tree1 ∷ st1) (λ _ _ _ → Lift n ⊤)
    Post = record { tree0 = replacePR.tree0 Pre ; ti = replacePR.ti Pre ; si = repl10 ; ri = repl12 _ (replacePR.si Pre) refl  ;  rti = lem14 ; ci = lift tt } where
         repl10 : stackInvariant key tree1 (replacePR.tree0 Pre) (tree1 ∷ st1)
         repl10 = popStackInvariant _ _ _ _ _  (subst (λ k → stackInvariant  key k (replacePR.tree0 Pre) (nd ∷ tree1 ∷ st1) ) 
             (sym (si-property1 (replacePR.si Pre)))  (replacePR.si Pre) )
         repl12 : (stack : List (bt A)) → stackInvariant key tree (replacePR.tree0 Pre) stack → stack ≡ (nd ∷ tree1 ∷ st1) 
             → replacedTree key value (child-replaced key tree1) (node key₁ value left right)
         repl12 _ s-nil ()
         repl12 (leaf ∷ st₁) (s-right .leaf .(replacePR.tree0 Pre) tree₁ {key₂} {v₂} x si) ()
         repl12 (node k₁ v₁ left₂ right₂ ∷ st₁) (s-right .(node k₁ v₁ left₂ right₂) .(replacePR.tree0 Pre) tree₁  {key₂} {v₂} x si) eq = lem13 where
            lem20 : node k₁ v₁ left₂ right₂ ≡ node key₁ value₁ left right 
            lem20 = ∷-injectiveˡ eq
            lem21 : tree1 ≡ node key₂ v₂ tree₁ (node k₁ v₁ left₂ right₂)
            lem21 = (si-property1 (subst₂ (λ j k →  stackInvariant key _ j  k ) refl (∷-injectiveʳ eq) si ))
            lem10 : node key value₁ left right ≡ child-replaced key tree1
            lem10 = begin
                node key value₁ left right ≡⟨ cong (λ k → node k value₁ left right ) b ⟩
                node key₁ value₁ left right ≡⟨ sym lem20 ⟩ 
                node k₁ v₁ left₂ right₂ ≡⟨ sym ( child-replaced-right x) ⟩
                child-replaced key (node key₂ v₂ tree₁ (node k₁ v₁ left₂ right₂)) ≡⟨ cong (child-replaced key) (sym lem21) ⟩
                child-replaced key tree1 ∎ where 
                  open ≡-Reasoning
            lem13 : replacedTree key value (child-replaced key tree1) (node key₁ value left right)
            lem13 = subst₂ (λ j k → replacedTree key value j (node k value left right) ) lem10 b r-node
         repl12 (leaf ∷ st₁) (s-left .tree .(replacePR.tree0 Pre) tree₁ {key₂} {v₂} x si) ()
         repl12 (node k₁ v₁ left₂ right₂ ∷ st₁) (s-left .(node k₁ v₁ left₂ right₂) .(replacePR.tree0 Pre) tree₁ {key₂} {v₂} x si) eq = lem13 where
            lem20 : node k₁ v₁ left₂ right₂ ≡ node key₁ value₁ left right 
            lem20 = ∷-injectiveˡ eq
            lem21 : tree1 ≡ node key₂ v₂ (node k₁ v₁ left₂ right₂) tree₁
            lem21 = (si-property1 (subst₂ (λ j k →  stackInvariant key _ j  k ) refl (∷-injectiveʳ eq) si ))
            lem10 : node key value₁ left right ≡ child-replaced key tree1
            lem10 = begin
                node key value₁ left right ≡⟨ cong (λ k → node k value₁ left right ) b ⟩
                node key₁ value₁ left right ≡⟨ sym lem20 ⟩ 
                node k₁ v₁ left₂ right₂ ≡⟨ sym ( child-replaced-left x) ⟩
                child-replaced key (node key₂ v₂ (node k₁ v₁ left₂ right₂) tree₁ ) ≡⟨ cong (child-replaced key) (sym lem21) ⟩
                child-replaced key tree1 ∎ where 
                  open ≡-Reasoning
            lem13 : replacedTree key value (child-replaced key tree1) (node key₁ value left right)
            lem13 = subst₂ (λ j k → replacedTree key value j (node k value left right) ) lem10 b r-node
         lem14 : treeInvariant (node key₁ value left right)
         lem14 = RTtoTI0 _ _ _ _ (child-repaced-ti key tree1 (siToTreeinvariant _ tree1 _ _ (replacePR.ti Pre) repl10 )) (repl12 _ (replacePR.si Pre) refl)
... | tri> ¬a ¬b c = next key value (node key₁ value₁ left repl ) st Post ≤-refl where
    Post : replacePR key value tree1 (node key₁ value₁ left repl ) st (λ _ _ _ → Lift n ⊤)
    Post = record { tree0 = replacePR.tree0 Pre ; ti = replacePR.ti Pre ; si = repl10 ; ri = repl12 _ (replacePR.si Pre) refl ;  rti = lem14 ; ci = lift tt } where
         repl10 : stackInvariant key tree1 (replacePR.tree0 Pre) (tree1 ∷ st1)
         repl10 = popStackInvariant _ _ _ _ _  (subst (λ k → stackInvariant  key k (replacePR.tree0 Pre) (nd ∷ tree1 ∷ st1) ) 
             (sym (si-property1 (replacePR.si Pre)))  (replacePR.si Pre) )
         repl12 : (stack : List (bt A)) → stackInvariant key tree (replacePR.tree0 Pre) stack → stack ≡ (nd ∷ tree1 ∷ st1) 
             → replacedTree key value (child-replaced key tree1) (node key₁ value₁ left repl )
         repl12 _ s-nil ()
         repl12 (leaf ∷ st₁) (s-right .leaf .(replacePR.tree0 Pre) tree₁ {key₂} {v₂} x si) ()
         repl12 (node k₁ v₁ left₂ right₂ ∷ st₁) (s-right .(node k₁ v₁ left₂ right₂) .(replacePR.tree0 Pre) tree₁  {key₂} {v₂} x si) eq = lem13 where
            lem20 : node k₁ v₁ left₂ right₂ ≡ node key₁ value₁ left right 
            lem20 = ∷-injectiveˡ eq
            lem21 : tree1 ≡ node key₂ v₂ tree₁ (node k₁ v₁ left₂ right₂)
            lem21 = (si-property1 (subst₂ (λ j k →  stackInvariant key _ j  k ) refl (∷-injectiveʳ eq) si ))
            lem10 : node key₁ value₁ left (child-replaced key (node k₁ v₁ left₂ right₂)) ≡ child-replaced key tree1
            lem10 = begin
                node key₁ value₁ left (child-replaced key (node k₁ v₁ left₂ right₂)) ≡⟨ cong ( λ k → node key₁ value₁ left k ) ( child-replaced-right repl13 ) ⟩
                node key₁ value₁ left right₂  ≡⟨ cong ( λ k → node key₁ value₁ left k ) (just-injective (cong node-right lem20)) ⟩
                node key₁ value₁ left right  ≡⟨ sym lem20 ⟩ 
                node k₁ v₁ left₂ right₂ ≡⟨ sym ( child-replaced-right x) ⟩
                child-replaced key (node key₂ v₂ tree₁ (node k₁ v₁ left₂ right₂)) ≡⟨ sym ( cong (child-replaced key ) lem21 ) ⟩ 
                child-replaced key tree1 ∎ where 
                  open ≡-Reasoning
                  repl13 : k₁ < key 
                  repl13 = subst (λ k → k < key) (sym (just-injective (cong node-key lem20))) c
            lem13 :  replacedTree key value (child-replaced key tree1) (node key₁ value₁ left repl )
            lem13 = subst (λ k → replacedTree key value k (node key₁ value₁ left repl ) ) lem10  (r-right c (replacePR.ri Pre))
         repl12 (leaf ∷ st₁) (s-left .tree .(replacePR.tree0 Pre) tree₁ {key₂} {v₂} x si) ()
         repl12 (node k₁ v₁ left₂ right₂ ∷ st₁) (s-left .(node k₁ v₁ left₂ right₂) .(replacePR.tree0 Pre) tree₁ {key₂} {v₂} x si) eq = lem13 where
            lem20 : node k₁ v₁ left₂ right₂ ≡ node key₁ value₁ left right 
            lem20 = ∷-injectiveˡ eq
            lem21 : tree1 ≡ node key₂ v₂ (node k₁ v₁ left₂ right₂) tree₁
            lem21 = (si-property1 (subst₂ (λ j k →  stackInvariant key _ j  k ) refl (∷-injectiveʳ eq) si ))
            lem10 : node key₁ value₁ left (child-replaced key (node k₁ v₁ left₂ right₂)) ≡ child-replaced key tree1
            lem10 = begin
                node key₁ value₁ left (child-replaced key (node k₁ v₁ left₂ right₂)) ≡⟨ cong ( λ k → node key₁ value₁ left k ) ( child-replaced-right repl13 ) ⟩
                node key₁ value₁ left right₂  ≡⟨ cong ( λ k → node key₁ value₁ left k ) (just-injective (cong node-right lem20)) ⟩
                node key₁ value₁ left right  ≡⟨ sym lem20 ⟩ 
                node k₁ v₁ left₂ right₂ ≡⟨ sym ( child-replaced-left x) ⟩
                child-replaced key (node key₂ v₂ (node k₁ v₁ left₂ right₂) tree₁ ) ≡⟨ sym ( cong (child-replaced key ) lem21 ) ⟩ 
                child-replaced key tree1 ∎ where 
                  open ≡-Reasoning
                  repl13 : k₁ < key
                  repl13 = subst (λ k → k < key) (sym (just-injective (cong node-key lem20))) c
            lem13 : replacedTree key value (child-replaced key tree1) (node key₁ value₁ left repl )
            lem13 = subst (λ k → replacedTree key value k (node key₁ value₁ left repl ) ) lem10  (r-right c (replacePR.ri Pre))
         lem14 : treeInvariant (node key₁ value₁ left repl )
         lem14 = RTtoTI0 _ _ _ _ (child-repaced-ti key tree1 (siToTreeinvariant _ tree1 _ _ (replacePR.ti Pre) repl10 )) (repl12 _ (replacePR.si Pre) refl)

TerminatingLoopS : {l m : Level} {t : Set l} (Index : Set m ) → {Invraiant : Index → Set m } → ( reduce : Index → ℕ)
   → (r : Index) → (p : Invraiant r)
   → (loop : (r : Index)  → Invraiant r → (next : (r1 : Index)  → Invraiant r1 → reduce r1 < reduce r  → t ) → t) → t
TerminatingLoopS {_} {_} {t} Index {Invraiant} reduce r p loop with <-cmp 0 (reduce r)
... | tri≈ ¬a b ¬c = loop r p (λ r1 p1 lt → ⊥-elim (nat-≡< b (≤-trans (s≤s z≤n) lt ) ) ) 
... | tri< a ¬b ¬c = loop r p (λ r1 p1 lt1 → TerminatingLoop1 (reduce r) r r1 (m≤n⇒m≤1+n lt1) p1 lt1 ) where
    TerminatingLoop1 : (j : ℕ) → (r r1 : Index) → reduce r1 < suc j  → Invraiant r1 →  reduce r1 < reduce r → t
    TerminatingLoop1 zero r r1 n≤j p1 lt = loop r1 p1 (λ r2 p1 lt1 → ⊥-elim (nat-≤> (≤-trans (s≤s z≤n) lt1) n≤j ) )
    TerminatingLoop1 (suc j) r r1  n≤j p1 lt with <-cmp (reduce r1) (suc j)
    ... | tri< a ¬b ¬c = TerminatingLoop1 j r r1 a p1 lt
    ... | tri≈ ¬a b ¬c = loop r1 p1 (λ r2 p2 lt1 → TerminatingLoop1 j r1 r2 (subst (λ k → reduce r2 < k ) b lt1 ) p2 lt1 )
    ... | tri> ¬a ¬b c =  ⊥-elim ( nat-≤> c n≤j )


insertTreeP : {n m : Level} {A : Set n} {t : Set m} → (tree : bt A) → (key : ℕ) → (value : A) → treeInvariant tree
     → (exit : (tree repl : bt A) → treeInvariant repl ∧ replacedTree key value tree repl → t ) → t
insertTreeP {n} {m} {A} {t} tree key value P0 exit =
   TerminatingLoopS (bt A ∧ List (bt A) ) {λ p → treeInvariant (proj1 p) ∧ stackInvariant key (proj1 p) tree (proj2 p) } (λ p → bt-depth (proj1 p)) ⟪ tree , tree ∷ [] ⟫  ⟪ P0 , s-nil ⟫
       $ λ p P loop → findP key (proj1 p)  tree (proj2 p) P (λ t s P1 lt → loop ⟪ t ,  s  ⟫ P1 lt )
       $ λ t s P C → replaceNodeP key value t C (proj1 P)
       $ λ t1 P1 R → TerminatingLoopS (List (bt A) ∧ bt A ∧ bt A )
            {λ p → replacePR key value  (proj1 (proj2 p)) (proj2 (proj2 p)) (proj1 p)  (λ _ _ _ → Lift n ⊤ ) }
               (λ p → length (proj1 p)) ⟪ s , ⟪ t , t1 ⟫ ⟫ record { tree0 = tree ; ti = P0 ; si = proj2 P ; rti = P1 ; ri = R ; ci = lift tt }
       $  λ p P1 loop → replaceP key value  (proj2 (proj2 p)) (proj1 p) P1
            (λ key value {tree1} repl1 stack P2 lt → loop ⟪ stack , ⟪ tree1 , repl1  ⟫ ⟫ P2 lt )
       $ λ tree repl P → exit tree repl P

insertTestP1 = insertTreeP leaf 1 1 t-leaf
  $ λ _ x0 P0 → insertTreeP x0 2 1 (proj1 P0)
  $ λ _ x1 P1 → insertTreeP x1 3 2 (proj1 P1)
  $ λ _ x2 P2 → insertTreeP x2 2 2 (proj1 P2) (λ _ x P  → x )


-- is realy inserted?

-- other element is preserved?

-- deletion?

