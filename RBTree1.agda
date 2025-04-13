{-# OPTIONS  --allow-unsolved-metas --cubical-compatible  #-}
module RBTree1 where

open import Level hiding (suc ; zero ; _⊔_ )

open import Data.Nat hiding (compare)
open import Data.Nat.Properties as NatProp
open import Data.Maybe
open import Data.Maybe.Properties
open import Data.Empty
open import Data.Unit
open import Data.List
open import Data.List.Properties
open import Data.Product

open import Function as F hiding (const)

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import logic
open import nat

open import BTree
open import RBTreeBase

open _∧_


RB→t2notLeaf : {n : Level} {A : Set n} {key : ℕ} {value : A} → (t₁ t₂ : bt (Color ∧ A) ) → (rbt : replacedRBTree key value t₁ t₂) → IsNode t₂ 
RB→t2notLeaf {n} {A} {k} {v} .leaf .(node k ⟪ Red , v ⟫ leaf leaf) rbr-leaf = record { key = k ; value = ⟪ Red , v ⟫ ; left = leaf ; right = leaf ; t=node = refl } 
RB→t2notLeaf {n} {A} {k} {v} .(node k ⟪ _ , _ ⟫ _ _) .(node k ⟪ _ , v ⟫ _ _) rbr-node = record { key = k ; value = ⟪ _ , v ⟫ ; left = _ ; right = _ ; t=node = refl }
RB→t2notLeaf {n} {A} {k} {v} .(node _ ⟪ _ , _ ⟫ _ _) .(node _ ⟪ _ , _ ⟫ _ _) (rbr-right x x₁ rbt) = record { key = _ ; value = _ ; left = _ ; right = _; t=node = refl }
RB→t2notLeaf {n} {A} {k} {v} .(node _ ⟪ _ , _ ⟫ _ _) .(node _ ⟪ _ , _ ⟫ _ _) (rbr-left x x₁ rbt) = record { key = _ ; value = _ ; left = _ ; right = _; t=node = refl }
RB→t2notLeaf {n} {A} {k} {v} .(node _ ⟪ Black , _ ⟫ _ _) .(node _ ⟪ Black , _ ⟫ _ _) (rbr-black-right x x₁ rbt) = record { key = _ ; value = _ ; left = _ ; right = _; t=node = refl }
RB→t2notLeaf {n} {A} {k} {v} .(node _ ⟪ Black , _ ⟫ _ _) .(node _ ⟪ Black , _ ⟫ _ _) (rbr-black-left x x₁ rbt) = record { key = _ ; value = _ ; left = _ ; right = _; t=node = refl }
RB→t2notLeaf {n} {A} {k} {v} .(node _ ⟪ Black , _ ⟫ (node _ ⟪ Red , _ ⟫ _ _) _) .(node _ ⟪ Red , _ ⟫ (node _ ⟪ Black , _ ⟫ _ _) (to-black _)) (rbr-flip-ll x x₁ x₂ rbt) = record { key = _ ; value = _ ; left = _ ; right = _; t=node = refl }
RB→t2notLeaf {n} {A} {k} {v} .(node _ ⟪ Black , _ ⟫ (node _ ⟪ Red , _ ⟫ _ _) _) .(node _ ⟪ Red , _ ⟫ (node _ ⟪ Black , _ ⟫ _ _) (to-black _)) (rbr-flip-lr x x₁ x₂ x₃ rbt) = record { key = _ ; value = _ ; left = _ ; right = _; t=node = refl }
RB→t2notLeaf {n} {A} {k} {v} .(node _ ⟪ Black , _ ⟫ _ (node _ ⟪ Red , _ ⟫ _ _)) .(node _ ⟪ Red , _ ⟫ (to-black _) (node _ ⟪ Black , _ ⟫ _ _)) (rbr-flip-rl x x₁ x₂ x₃ rbt) = record { key = _ ; value = _ ; left = _ ; right = _; t=node = refl }
RB→t2notLeaf {n} {A} {k} {v} .(node _ ⟪ Black , _ ⟫ _ (node _ ⟪ Red , _ ⟫ _ _)) .(node _ ⟪ Red , _ ⟫ (to-black _) (node _ ⟪ Black , _ ⟫ _ _)) (rbr-flip-rr x x₁ x₂ rbt) = record { key = _ ; value = _ ; left = _ ; right = _; t=node = refl }
RB→t2notLeaf {n} {A} {k} {v} .(node _ ⟪ Black , _ ⟫ (node _ ⟪ Red , _ ⟫ _ _) _) .(node _ ⟪ Black , _ ⟫ _ (node _ ⟪ Red , _ ⟫ _ _)) (rbr-rotate-ll x x₁ rbt) = record { key = _ ; value = _ ; left = _ ; right = _; t=node = refl }
RB→t2notLeaf {n} {A} {k} {v} .(node _ ⟪ Black , _ ⟫ _ (node _ ⟪ Red , _ ⟫ _ _)) .(node _ ⟪ Black , _ ⟫ (node _ ⟪ Red , _ ⟫ _ _) _) (rbr-rotate-rr x x₁ rbt) = record { key = _ ; value = _ ; left = _ ; right = _; t=node = refl }
RB→t2notLeaf {n} {A} {k} {v} .(node kg ⟪ Black , _ ⟫ (node kp ⟪ Red , _ ⟫ _ _) _) .(node kn ⟪ Black , _ ⟫ (node kp ⟪ Red , _ ⟫ _ t₂) (node kg ⟪ Red , _ ⟫ t₃ _)) (rbr-rotate-lr t₂ t₃ kg kp kn x x₁ x₂ rbt) = record { key = kn ; value = ⟪ Black , _ ⟫ ; left = _ ; right = _; t=node = refl }
RB→t2notLeaf {n} {A} {k} {v} .(node kg ⟪ Black , _ ⟫ _ (node kp ⟪ Red , _ ⟫ _ _)) .(node kn ⟪ Black , _ ⟫ (node kg ⟪ Red , _ ⟫ _ t₂) (node kp ⟪ Red , _ ⟫ t₃ _)) (rbr-rotate-rl t₂ t₃ kg kp kn x x₁ x₂ rbt) = record { key = kn ; value = ⟪ Black , _ ⟫ ; left = _ ; right = _; t=node = refl }


tree-construct : {n : Level} (A : Set n) {vg : A} {kg : ℕ} → (uncle t : bt A ) → tr< kg uncle → tr> kg t
  → treeInvariant uncle → treeInvariant t → treeInvariant (node kg vg uncle t)
tree-construct A {vg} {kg} uncle t ux tx ui ti with node→leaf∨IsNode t | node→leaf∨IsNode uncle
... | case1 teq | case1 ueq = subst treeInvariant (node-cong refl refl (sym ueq)  (sym teq) ) (t-single _ _)
... | case1 teq | case2 un = subst treeInvariant (node-cong refl refl (sym (IsNode.t=node un)) (sym teq)  ) (t-left _ _
    (proj1 rr11) (proj1 (proj2 rr11)) (proj2 (proj2 rr11)) (subst treeInvariant (IsNode.t=node un) ui)) where
      rr11 : (IsNode.key un < kg ) ∧ tr< kg (IsNode.left un) ∧ tr< kg (IsNode.right un)
      rr11 = subst (λ k → tr< kg k) (IsNode.t=node un) ux
... | case2 tn | case1 ueq = subst treeInvariant (node-cong refl refl (sym ueq) (sym (IsNode.t=node tn)) ) (t-right _ _
    (proj1 rr12) (proj1 (proj2 rr12)) (proj2 (proj2 rr12)) (subst treeInvariant (IsNode.t=node tn) ti)) where
      rr12 : (kg < IsNode.key tn ) ∧ tr> kg (IsNode.left tn) ∧ tr> kg (IsNode.right tn)
      rr12 = subst (λ k → tr> kg k) (IsNode.t=node tn) tx
... | case2 tn | case2 un = subst treeInvariant (node-cong refl refl (sym (IsNode.t=node un)) (sym (IsNode.t=node tn)) ) (t-node _ _ _
    (proj1 rr11) (proj1 rr12) (proj1 (proj2 rr11)) (proj2 (proj2 rr11)) (proj1 (proj2 rr12)) (proj2 (proj2 rr12))
       (subst treeInvariant (IsNode.t=node un) ui) (subst treeInvariant (IsNode.t=node tn) ti)) where
      rr11 : (IsNode.key un < kg ) ∧ tr< kg (IsNode.left un) ∧ tr< kg (IsNode.right un)
      rr11 = subst (λ k → tr< kg k) (IsNode.t=node un) ux
      rr12 : (kg < IsNode.key tn ) ∧ tr> kg (IsNode.left tn) ∧ tr> kg (IsNode.right tn)
      rr12 = subst (λ k → tr> kg k) (IsNode.t=node tn) tx

treeInvariant-to-black : {n : Level} (A : Set n)  → {t : bt (Color ∧ A) } →
  treeInvariant t → treeInvariant (to-black t)
treeInvariant-to-black A {.leaf} t-leaf = t-leaf
treeInvariant-to-black A {.(node key value leaf leaf)} (t-single key value) = t-single _ _
treeInvariant-to-black A {.(node key _ leaf (node key₁ _ _ _))} (t-right key key₁ x x₁ x₂ ti) = t-right key key₁ x x₁ x₂ ti
treeInvariant-to-black A {.(node key₁ _ (node key _ _ _) leaf)} (t-left key key₁ x x₁ x₂ ti) = t-left key key₁ x x₁ x₂ ti
treeInvariant-to-black A {.(node key₁ _ (node key _ _ _) (node key₂ _ _ _))} (t-node key key₁ key₂ x x₁ x₂ x₃ x₄ x₅ ti ti₁) =
   t-node key key₁ key₂ x x₁ x₂ x₃ x₄ x₅ ti ti₁

RB-repl→ti-lem01 : {n : Level} {A : Set n} {key : ℕ} {value : A} (ca : Color) (value₂ : A) (t t₁ : bt (Color ∧ A))  
      → treeInvariant (node key ⟪ ca , value₂ ⟫ t t₁) → treeInvariant (node key ⟪ ca , value ⟫ t t₁)
RB-repl→ti-lem01 {n} {A} {key} {value} ca value₂ t t₁ ti = replaceTree1 _ _ _ ti

RB-repl→ti-lem02 : {n : Level } {A : Set n} {key k : ℕ} {v1 value : A} {ca : Color} {t t1 t2 : bt (Color ∧ A)} (x : color t2 ≡ color t) (x₁ : k < key) (rbt : replacedRBTree key value t2 t) →
            (treeInvariant t2 → treeInvariant t) → treeInvariant (node k ⟪ ca , v1 ⟫ t1 t2) → treeInvariant (node k ⟪ ca , v1 ⟫ t1 t)
RB-repl→ti-lem02 {n} {A} {key} {k} {v1} {value} {ca} {t} {t₁} {t₂} ceq x₁ rbt prev ti = lem21 where
  rr04 : tr< k t₁ 
  rr04 = proj1 (ti-property1 ti)
  rr02 : tr> k t 
  rr02 = RB-repl→ti> _ _ _ _ _ rbt x₁ (proj2 (ti-property1 ti))
  lem21 : treeInvariant (node k ⟪ ca , v1 ⟫ t₁ t)
  lem21 = tree-construct _ _ _ rr04 rr02 (treeLeftDown _ _ ti) (prev (treeRightDown _ _ ti)) 

RB-repl→ti-lem03 : {n : Level} {A : Set n} {key k : ℕ} {value v1 : A} {ca : Color} {t t₁ t₂ : bt (Color ∧ A)} (x : color t₁ ≡ color t) (x₁ : key < k) 
   (rbt : replacedRBTree key value t₁ t) → (treeInvariant t₁ → treeInvariant t) 
   → treeInvariant (node k ⟪ ca , v1 ⟫ t₁ t₂) → treeInvariant (node k ⟪ ca , v1 ⟫ t t₂)
RB-repl→ti-lem03 {n} {A} {key} {k} {value} {v1} {ca} {t} {t₁} {t₂} ceq x₁ rbt prev ti = lem21 where
  lem22 : treeInvariant t
  lem22 = prev (treeLeftDown _ _ ti)
  rr04 : tr> k t₂ 
  rr04 = proj2 (ti-property1 ti)
  rr02 : tr< k t 
  rr02 = RB-repl→ti< _ _ _ _ _ rbt x₁ (proj1 (ti-property1 ti))
  lem21 : treeInvariant (node k ⟪ ca , v1 ⟫ t t₂)
  lem21 = tree-construct _ _ _ rr02 rr04 lem22 (treeRightDown _ _ ti)

RB-repl→ti-lem04 : {n : Level} {A : Set n} {key : ℕ} {value : A} {t t₁ t₂ : bt (Color ∧ A)} {value₁ : A} {key₁ : ℕ} (x : color t₂ ≡ Red) (x₁ : key₁ < key)
    (rbt : replacedRBTree key value t₁ t₂) → (treeInvariant t₁ → treeInvariant t₂) → treeInvariant (node key₁ ⟪ Black , value₁ ⟫ t t₁) 
    → treeInvariant (node key₁ ⟪ Black , value₁ ⟫ t t₂)
RB-repl→ti-lem04 {n} {A} {key} {value} {t} {t₁} {t₂} {value₁} {key₁} ceq x₁ rbt prev ti = lem21 where
  lem22 : treeInvariant t₂
  lem22 = prev (treeRightDown _ _ ti)
  rr04 : tr< key₁ t
  rr04 = proj1 (ti-property1 ti)
  rr02 : tr> key₁ t₂ 
  rr02 = RB-repl→ti> _ _ _ _ _ rbt x₁ (proj2 (ti-property1 ti))
  lem21 : treeInvariant (node key₁ ⟪ Black , value₁ ⟫ t t₂)
  lem21 = tree-construct _ _ _ rr04 rr02 (treeLeftDown _ _ ti) lem22

RB-repl→ti-lem05 : {n : Level} {A : Set n} {key : ℕ} {value : A} {t t₁ t₂ : bt (Color ∧ A)} {value₁ : A} {key₁ : ℕ} (x : color t₂ ≡ Red) (x₁ : key < key₁)
    (rbt : replacedRBTree key value t₁ t₂) → (treeInvariant t₁ → treeInvariant t₂) → treeInvariant (node key₁ ⟪ Black , value₁ ⟫ t₁ t) 
     → treeInvariant (node key₁ ⟪ Black , value₁ ⟫ t₂ t)
RB-repl→ti-lem05 {n} {A} {key} {value} {t} {t₁} {t₂} {value₁} {key₁} ceq x₁ rbt prev ti = lem21 where
  lem22 : treeInvariant t₂
  lem22 = prev (treeLeftDown _ _ ti )
  rr03 : tr< key₁ t₁
  rr03 = proj1 (ti-property1 ti)
  rr04 : tr> key₁ t
  rr04 = proj2 (ti-property1 ti)
  rr02 : tr< key₁ t₂ 
  rr02 = RB-repl→ti< _ _ _ _ _ rbt x₁ rr03
  lem21 : treeInvariant (node key₁ ⟪ Black , value₁ ⟫ t₂ t)
  lem21 = tree-construct _ _ _ rr02 rr04 lem22 (treeRightDown _ _ ti) 

RB-repl→ti-lem06 : {n : Level} {A : Set n} {key : ℕ} {value : A} {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A} (x : color t₂ ≡ Red) 
   (x₁ : color uncle ≡ Red) (x₂ : key < kp) (rbt : replacedRBTree key value t₁ t₂) → (treeInvariant t₁ → treeInvariant t₂) 
   → treeInvariant (node kg ⟪ Black , vg ⟫ (node kp ⟪ Red , vp ⟫ t₁ t) uncle) 
   → treeInvariant (node kg ⟪ Red , vg ⟫ (node kp ⟪ Black , vp ⟫ t₂ t) (to-black uncle))
RB-repl→ti-lem06 {n} {A} {key} {value} {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} ceq ueq x₀ rbt prev ti 
     = lem21 where 
  lem22 : treeInvariant t₂
  lem22 = prev (treeLeftDown _ _ (treeLeftDown _ _ ti ))
  lem25 : treeInvariant t
  lem25 = treeRightDown _ _ (treeLeftDown _ _ ti)
  rr05 : (kp < kg) ∧ tr< kg t₁ ∧ tr< kg t 
  rr05 = proj1 (ti-property1 ti)
  rr07 : tr> kg uncle
  rr07 = proj2 (ti-property1 ti)
  rr08 : tr> kp t
  rr08 = proj2 (ti-property1 (treeLeftDown _ _ ti))
  rr10 : tr< kp t₁
  rr10 = proj1 (ti-property1 (treeLeftDown _ _ ti))
  rr09 : tr< kg t₂
  rr09 = RB-repl→ti< _ _ _ _ _ rbt (<-trans x₀ (proj1 rr05)) (proj1 (proj2 rr05))
  rr11 : tr< kp t₂
  rr11 = RB-repl→ti< _ _ _ _ _ rbt x₀ rr10
  lem21 : treeInvariant (node kg ⟪ Red , vg ⟫ (node kp ⟪ Black , vp ⟫ t₂ t) (to-black uncle))
  lem21 = tree-construct _ _ _ ⟪ proj1 rr05 , ⟪ rr09 , proj2 (proj2 rr05) ⟫ ⟫  (tr>-to-black rr07) (tree-construct _ _ _ rr11 rr08 lem22 lem25) 
     (treeInvariant-to-black A (treeRightDown _ _ ti) ) 

RB-repl→ti-lem07 : {n : Level} {A : Set n} {key : ℕ} {value : A}  {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A}
    (x : color t₂ ≡ Red) (x₁ : color uncle ≡ Red) (x₂ : kp < key) (x₃ : key < kg) (rbt : replacedRBTree key value t₁ t₂) → (treeInvariant t₁ → treeInvariant t₂)
    → treeInvariant (node kg ⟪ Black , vg ⟫ (node kp ⟪ Red , vp ⟫ t t₁) uncle)
    → treeInvariant (node kg ⟪ Red , vg ⟫ (node kp ⟪ Black , vp ⟫ t t₂) (to-black uncle))
RB-repl→ti-lem07 {n} {A} {key} {value} {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} ceq ueq x₀ x₁ rbt prev ti
     = lem21 where
  lem22 : treeInvariant t₂
  lem22 = prev (treeRightDown _ _ (treeLeftDown _ _ ti ))
  lem25 : treeInvariant t
  lem25 = treeLeftDown _ _ (treeLeftDown _ _ ti)
  rr05 : (kp < kg) ∧ tr< kg t ∧ tr< kg t₁ 
  rr05 = proj1 (ti-property1 ti)
  rr07 : tr> kg uncle
  rr07 = proj2 (ti-property1 ti)
  rr08 : tr< kp t
  rr08 = proj1 (ti-property1 (treeLeftDown _ _ ti))
  rr10 : tr> kp t₁
  rr10 = proj2 (ti-property1 (treeLeftDown _ _ ti))
  rr09 : tr> kp t₂
  rr09 = RB-repl→ti> _ _ _ _ _ rbt x₀ rr10
  rr11 : tr< kg t₂
  rr11 = RB-repl→ti< _ _ _ _ _ rbt x₁ (proj2 (proj2 rr05))
  lem21 : treeInvariant (node kg ⟪ Red , vg ⟫ (node kp ⟪ Black , vp ⟫ t t₂) (to-black uncle))
  lem21 = tree-construct _ _ _ ⟪ proj1 rr05 , ⟪ proj1 (proj2 rr05) , rr11 ⟫ ⟫  (tr>-to-black rr07) 
     (tree-construct _ _ _ rr08 rr09 lem25 lem22) (treeInvariant-to-black A (treeRightDown _ _ ti) )

RB-repl→ti-lem08 : {n : Level} {A : Set n} {key : ℕ} {value : A}  → {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A}
     (x : color t₂ ≡ Red) (x₁ : color uncle ≡ Red) (x₂ : kg < key) (x₃ : key < kp) (rbt : replacedRBTree key value t₁ t₂)
     → (treeInvariant t₁ → treeInvariant t₂) → treeInvariant (node kg ⟪ Black , vg ⟫ uncle            (node kp ⟪ Red ,   vp ⟫ t₁ t))
                                             → treeInvariant (node kg ⟪ Red ,   vg ⟫ (to-black uncle) (node kp ⟪ Black , vp ⟫ t₂ t))
RB-repl→ti-lem08 {n} {A} {key} {value} {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} ceq ueq x₀ x₁ rbt prev ti = lem21 where
  lem22 : treeInvariant t₂
  lem22 = prev (treeLeftDown _ _ (treeRightDown _ _ ti ))
  lem25 : treeInvariant t
  lem25 = treeRightDown _ _ (treeRightDown _ _ ti)
  rr05 : (kg < kp) ∧ tr> kg t₁ ∧ tr> kg t
  rr05 = proj2 (ti-property1 ti)
  rr07 : tr< kg uncle
  rr07 = proj1 (ti-property1 ti)
  rr08 : tr> kp t
  rr08 = proj2 (ti-property1 (treeRightDown _ _ ti))
  rr10 : tr< kp t₁
  rr10 = proj1 (ti-property1 (treeRightDown _ _ ti))
  rr09 : tr< kp t₂
  rr09 = RB-repl→ti< _ _ _ _ _ rbt x₁ rr10
  rr11 : tr> kg t₂
  rr11 = RB-repl→ti> _ _ _ _ _ rbt x₀ (proj1 (proj2 rr05))
  lem21 : treeInvariant (node kg ⟪ Red ,   vg ⟫ (to-black uncle) (node kp ⟪ Black , vp ⟫ t₂ t))
  lem21 = tree-construct _ _ _ (tr<-to-black rr07) ⟪ proj1 rr05 , ⟪ rr11 , proj2 (proj2 rr05) ⟫ ⟫ (treeInvariant-to-black A (treeLeftDown _ _ ti) )
         (tree-construct _ _ _ rr09 rr08 lem22 lem25)

RB-repl→ti-lem09 : {n : Level} {A : Set n} {key : ℕ} {value : A}  → {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A}
        (x : color t₂ ≡ Red) (x₁ : color uncle ≡ Red) (x₂ : kp < key) (rbt : replacedRBTree key value t₁ t₂) →
        (treeInvariant t₁ → treeInvariant t₂) → treeInvariant (node kg ⟪ Black , vg ⟫ uncle (node kp ⟪ Red , vp ⟫ t t₁)) →
        treeInvariant (node kg ⟪ Red , vg ⟫ (to-black uncle) (node kp ⟪ Black , vp ⟫ t t₂))
RB-repl→ti-lem09 {n} {A} {key} {value} {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} ceq ueq x₁ rbt prev ti = lem21  where
  lem22 : treeInvariant t₂
  lem22 = prev (treeRightDown _ _ (treeRightDown _ _ ti ))
  lem25 : treeInvariant t
  lem25 = treeLeftDown _ _ ( treeRightDown _ _ ti )
  rr05 : (kg < kp) ∧ tr> kg t ∧ tr> kg t₁
  rr05 = proj2 (ti-property1 ti)
  rr07 : tr< kg uncle
  rr07 = proj1 (ti-property1 ti)
  rr08 : tr> kp t₁
  rr08 = proj2 (ti-property1 (treeRightDown _ _ ti))
  rr10 : tr< kp t
  rr10 = proj1 (ti-property1 (treeRightDown _ _ ti))
  rr09 : tr> kp t₂
  rr09 = RB-repl→ti> _ _ _ _ _ rbt x₁ rr08
  lem21 : treeInvariant (node kg ⟪ Red , vg ⟫ (to-black uncle) (node kp ⟪ Black , vp ⟫ t t₂))
  lem21 = tree-construct _ _ _ (tr<-to-black rr07) ⟪ proj1 rr05 , ⟪ proj1 (proj2 rr05) , <-tr> rr09 (proj1 rr05) ⟫ ⟫
     (treeInvariant-to-black A (treeLeftDown _ _ ti) ) (tree-construct _ _ _ rr10 rr09 lem25 lem22)

RB-repl→ti-lem10 : {n : Level} {A : Set n} {key : ℕ} {value : A}  → {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A}
        (x : color t₂ ≡ Red) (x₁ : key < kp) (rbt : replacedRBTree key value t₁ t₂) →
        (treeInvariant t₁ → treeInvariant t₂) → treeInvariant (node kg ⟪ Black , vg ⟫ (node kp ⟪ Red , vp ⟫ t₁ t) uncle) →
        treeInvariant (node kp ⟪ Black , vp ⟫ t₂ (node kg ⟪ Red , vg ⟫ t uncle))
RB-repl→ti-lem10 {n} {A} {key} {value} {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} ceq x₁ rbt prev ti =
      tree-construct _ _ _ rr09 ⟪ proj1 rr05 , ⟪ rr10 , <-tr> rr07 (proj1 rr05) ⟫ ⟫ lem22 (tree-construct _ _ _ (proj2 (proj2 rr05)) rr07 lem25 lem26) where
  lem22 : treeInvariant t₂
  lem22 = prev (treeLeftDown _ _ (treeLeftDown _ _ ti ) )
  lem25 : treeInvariant t
  lem25 = treeRightDown _ _ (treeLeftDown _ _ ti )
  lem26 : treeInvariant uncle
  lem26 = treeRightDown _ _ ti
  rr05 : (kp < kg) ∧ tr< kg t₁ ∧ tr< kg t
  rr05 = proj1 (ti-property1 ti)
  rr07 : tr> kg uncle
  rr07 = proj2 (ti-property1 ti)
  rr08 : tr< kp t₁
  rr08 = proj1 (ti-property1 (treeLeftDown _ _ ti))
  rr10 : tr> kp t
  rr10 = proj2 (ti-property1 (treeLeftDown _ _ ti))
  rr09 : tr< kp t₂
  rr09 = RB-repl→ti< _ _ _ _ _ rbt x₁ rr08


RB-repl→ti-lem11 : {n : Level} {A : Set n} {key : ℕ} {value : A}  → {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A}
        (x : color t₂ ≡ Red) (x₁ : kp < key) (rbt : replacedRBTree key value t₁ t₂) →
        (treeInvariant t₁ → treeInvariant t₂) → treeInvariant (node kg ⟪ Black , vg ⟫ uncle (node kp ⟪ Red , vp ⟫ t t₁)) →
        treeInvariant (node kp ⟪ Black , vp ⟫ (node kg ⟪ Red , vg ⟫ uncle t) t₂)
RB-repl→ti-lem11 {n} {A} {key} {value} {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} ceq x₁ rbt prev ti = lem21 where
  lem22 : treeInvariant t₂
  lem22 = prev (treeRightDown _ _ (treeRightDown _ _ ti ) )
  lem25 : treeInvariant t
  lem25 = treeLeftDown _ _ (treeRightDown _ _ ti )
  lem26 : treeInvariant uncle
  lem26 = treeLeftDown _ _ ti
  rr05 : (kg < kp) ∧ tr> kg t ∧ tr> kg t₁
  rr05 = proj2 (ti-property1 ti)
  rr07 : tr< kg uncle
  rr07 = proj1 (ti-property1 ti)
  rr08 : tr> kp t₁
  rr08 = proj2 (ti-property1 (treeRightDown _ _ ti))
  rr10 : tr< kp t
  rr10 = proj1 (ti-property1 (treeRightDown _ _ ti))
  rr09 : tr> kp t₂
  rr09 = RB-repl→ti> _ _ _ _ _ rbt x₁ rr08
  lem21 :  treeInvariant (node kp ⟪ Black , vp ⟫ (node kg ⟪ Red , vg ⟫ uncle t) t₂)
  lem21 = tree-construct _ _ _ ⟪ proj1 rr05 , ⟪ >-tr< rr07 (proj1 rr05) , rr10 ⟫ ⟫  rr09 (tree-construct _ _ _ rr07 (proj1 (proj2 rr05)) lem26 lem25) lem22


RB-repl→ti-lem12 : {n : Level} {A : Set n} {key : ℕ} {value : A}  → {t t₁ uncle : bt (Color ∧ A)} (t₂ t₃ : bt (Color ∧ A)) (kg kp kn : ℕ) {vg vp vn : A} (x : color t₃ ≡ Black)
        (x₁ : kp < key) (x₂ : key < kg) (rbt : replacedRBTree key value t₁ (node kn ⟪ Red , vn ⟫ t₂ t₃)) →
        (treeInvariant t₁ → treeInvariant (node kn ⟪ Red , vn ⟫ t₂ t₃)) → treeInvariant (node kg ⟪ Black , vg ⟫ (node kp ⟪ Red , vp ⟫ t t₁) uncle) →
        treeInvariant (node kn ⟪ Black , vn ⟫ (node kp ⟪ Red , vp ⟫ t t₂) (node kg ⟪ Red , vg ⟫ t₃ uncle))
RB-repl→ti-lem12 {n} {A} {key} {value} {t} {t₁} {uncle} t₂ t₃ kg kp kn {vg} {vp} {vn} ceq x₁ x₂ rbt prev ti =
             t-node _ _ _ (proj1 rr09) (proj1 rr11) (>-tr< rr10 (proj1 rr09)) rr24  rr22 (<-tr> rr07 (proj1 rr11) ) rr20 rr21  where
  lem22 : treeInvariant t₂
  lem22 = treeLeftDown _ _ (prev (treeRightDown _ _ (treeLeftDown _ _ ti ) ))
  lem23 : treeInvariant t₃
  lem23 = treeRightDown _ _ (prev (treeRightDown _ _ (treeLeftDown _ _ ti ) ))
  lem25 : treeInvariant t
  lem25 = treeLeftDown _ _ (treeLeftDown _ _ ti )
  lem26 : treeInvariant uncle
  lem26 = treeRightDown _ _ ti
  rr05 : (kp < kg) ∧ tr< kg t ∧ tr< kg t₁
  rr05 = proj1 (ti-property1 ti)
  rr07 : tr> kg uncle
  rr07 = proj2 (ti-property1 ti)
  rr08 : tr> kp t₁
  rr08 = proj2 (ti-property1 (treeLeftDown _ _ ti))
  rr10 : tr< kp t
  rr10 = proj1 (ti-property1 (treeLeftDown _ _ ti))
  rr09 : (kp < kn) ∧ tr> kp t₂ ∧ tr> kp  t₃
  rr09 = RB-repl→ti> _ _ _ _ _ rbt x₁ rr08
  rr11 : (kn < kg) ∧ tr< kg t₂ ∧ tr< kg t₃
  rr11 = RB-repl→ti< _ _ _ _ _ rbt x₂ (proj2 (proj2 rr05))
  rr20 : treeInvariant (node kp ⟪ Red , vp ⟫ t t₂)
  rr20 = tree-construct _ _ _ rr10 (proj1 (proj2 rr09)) lem25 lem22
  rr21 : treeInvariant (node kg ⟪ Red , vg ⟫ t₃ uncle)
  rr21 = tree-construct _ _ _ (proj2 (proj2 rr11)) rr07 lem23 lem26
  rr22 : tr> kn t₃
  rr22 = proj2 (ti-property1 (prev (treeRightDown _ _ (treeLeftDown _ _ ti )) ))
  rr24 : tr< kn t₂
  rr24 = proj1 (ti-property1 (prev (treeRightDown _ _ (treeLeftDown _ _ ti )) ))

RB-repl→ti-lem13 : {n : Level} {A : Set n} {key : ℕ} {value : A}  → {t t₁ uncle : bt (Color ∧ A)} (t₂ t₃ : bt (Color ∧ A)) (kg kp kn : ℕ) {vg vp vn : A} (x : color t₃ ≡ Black)
        (x₁ : kg < key) (x₂ : key < kp) (rbt : replacedRBTree key value t₁ (node kn ⟪ Red , vn ⟫ t₂ t₃)) →
        (treeInvariant t₁ → treeInvariant (node kn ⟪ Red , vn ⟫ t₂ t₃)) → treeInvariant (node kg ⟪ Black , vg ⟫ uncle (node kp ⟪ Red , vp ⟫ t₁ t)) →
        treeInvariant (node kn ⟪ Black , vn ⟫ (node kg ⟪ Red , vg ⟫ uncle t₂) (node kp ⟪ Red , vp ⟫ t₃ t))
RB-repl→ti-lem13 {n} {A} {key} {value} {t} {t₁} {uncle} t₂ t₃ kg kp kn {vg} {vp} {vn} ceq x₁ x₂ rbt prev ti =
             t-node _ _ _ (proj1 rr09) (proj1 rr11) (>-tr< rr07 (proj1 rr09)) rr24  rr22 (<-tr> rr10 (proj1 rr11)) rr20 rr21   where
  lem22 : treeInvariant t₂
  lem22 = treeLeftDown _ _ (prev (treeLeftDown _ _ (treeRightDown _ _ ti ) ))
  lem23 : treeInvariant t₃
  lem23 = treeRightDown _ _ (prev (treeLeftDown _ _ (treeRightDown _ _ ti ) ))
  lem25 : treeInvariant t
  lem25 = treeRightDown _ _ (treeRightDown _ _ ti )
  lem26 : treeInvariant uncle
  lem26 = treeLeftDown _ _ ti
  rr05 : (kg < kp) ∧ tr> kg t₁ ∧ tr> kg t
  rr05 = proj2 (ti-property1 ti)
  rr07 : tr< kg uncle
  rr07 = proj1 (ti-property1 ti)
  rr08 : tr< kp t₁
  rr08 = proj1 (ti-property1 (treeRightDown _ _ ti))
  rr10 : tr> kp t
  rr10 = proj2 (ti-property1 (treeRightDown _ _ ti))
  rr09 : (kg < kn) ∧ tr> kg t₂ ∧ tr> kg t₃
  rr09 = RB-repl→ti> _ _ _ _ _ rbt x₁ (proj1 (proj2 rr05))
  rr11 : (kn < kp) ∧ tr< kp t₂ ∧ tr< kp t₃
  rr11 = RB-repl→ti< _ _ _ _ _ rbt x₂ rr08
  rr20 : treeInvariant (node kg ⟪ Red , vg ⟫ uncle t₂)
  rr20 = tree-construct _ _ _ rr07 (proj1 (proj2 rr09)) lem26 lem22
  rr21 : treeInvariant (node kp ⟪ Red , vp ⟫ t₃ t)
  rr21 = tree-construct _ _ _ (proj2 (proj2 rr11)) rr10 lem23 lem25
  rr22 : tr> kn t₃
  rr22 = proj2 (ti-property1 (prev (treeLeftDown _ _ (treeRightDown _ _ ti ) ) ))
  rr24 : tr< kn t₂
  rr24 = proj1 (ti-property1 (prev (treeLeftDown _ _ (treeRightDown _ _ ti ) ) ))


RB-repl→ti : {n : Level} {A : Set n} → (tree repl : bt (Color ∧ A) ) → (key : ℕ ) → (value : A) → treeInvariant tree
       → replacedRBTree key value tree repl → treeInvariant repl
RB-repl→ti {n} {A} tree repl key value ti rbr = RBTI-induction A tree tree repl key value refl rbr {λ key value b a rbr → treeInvariant b → treeInvariant a }
     ⟪ lem00 , ⟪ RB-repl→ti-lem01 , ⟪ RB-repl→ti-lem02 , ⟪ RB-repl→ti-lem03  , ⟪ RB-repl→ti-lem04 , ⟪ RB-repl→ti-lem05 , 
       ⟪ RB-repl→ti-lem06 , ⟪ RB-repl→ti-lem07 , ⟪ RB-repl→ti-lem08 , ⟪ RB-repl→ti-lem09 , ⟪ RB-repl→ti-lem10 , ⟪ RB-repl→ti-lem11 
          , ⟪ RB-repl→ti-lem12 , RB-repl→ti-lem13 ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ti where
      lem00 : treeInvariant leaf → treeInvariant (node key ⟪ Red , value ⟫ leaf leaf)
      lem00 ti = t-single key ⟪ Red , value ⟫


si-property-4 : {n : Level} {A : Set n} → {key : ℕ } → (tree orig x : bt A ) → (st : List (bt A))  
    →  st ≡ x ∷ []
    →  stackInvariant key tree orig st
    → (x ≡ orig) ∧ (x ≡ tree)
si-property-4 {n} {A} {key} tree .tree x .(tree ∷ []) eq s-nil = ⟪ just-injective (cong head (sym eq)) , just-injective (cong head (sym eq)) ⟫
si-property-4 {n} {A} {key} tree orig x .(tree ∷ _) eq (s-right .tree .orig tree₁ x₁ si) = ⊥-elim ( si-property0 si (just-injective (cong tail eq)) )
si-property-4 {n} {A} {key} tree orig x .(tree ∷ _) eq (s-left .tree .orig tree₁ x₁ si) = ⊥-elim ( si-property0 si (just-injective (cong tail eq)) )

si-property-5 : {n : Level} {A : Set n} → {key : ℕ } → {tree orig x x₁ x₂ : bt A } → {st st' : List (bt A)} 
    → st ≡ x ∷ x₁ ∷ x₂ ∷ st'
    → stackInvariant key tree orig st
    → (¬ (x₁ ≡ leaf )) ∧ (¬ (x₂ ≡ leaf ))
si-property-5 {n} {A} {key} () s-nil
si-property-5 {n} {A} {key} () (s-right _ _ tree₁ lt s-nil)
si-property-5 {n} {A} {key} eq (s-right _ _ tree₁ lt (s-right .(node _ _ tree₁ _) _ tree₂ x₁ s-nil)) 
   = ⟪ (λ eq₁ → bt-ne (trans (sym eq₁) (sym ( just-injective (cong head (just-injective (cong tail eq))) )))) 
     , (λ eq₁ → bt-ne (trans (sym eq₁) (sym ( just-injective (cong head (just-injective (cong tail (just-injective (cong tail eq))) )))) )) ⟫ 
si-property-5 {n} {A} {key} {tree} {orig} {x} {x₁} {x₂} eq (s-right _ _ tree₁ lt si1@(s-right .(node _ _ tree₁ _) _ tree₂ lt₁ 
        (s-right .(node _ _ tree₂ (node _ _ tree₁ _)) _ tree₃ lt₂ si))) 
   = ⟪ (λ eq₁ → bt-ne (trans (sym eq₁) (sym ( just-injective (cong head (just-injective (cong tail eq))) )))) 
     , (λ eq₁ → bt-ne (trans (sym eq₁) (sym ( just-injective (cong head (just-injective (cong tail (just-injective (cong tail eq))) )))) )) ⟫ 
si-property-5 {n} {A} {key} eq (s-right _ _ tree₁ x (s-right .(node _ _ tree₁ _) _ tree₂ x₁ (s-left .(node _ _ tree₂ (node _ _ tree₁ _)) _ tree x₂ si))) 
   = ⟪ (λ eq₁ → bt-ne (trans (sym eq₁) (sym ( just-injective (cong head (just-injective (cong tail eq))) )))) 
     , (λ eq₁ → bt-ne (trans (sym eq₁) (sym ( just-injective (cong head (just-injective (cong tail (just-injective (cong tail eq))) )))) )) ⟫ 
si-property-5 {n} {A} {key} eq (s-right _ _ tree₁ x (s-left .(node _ _ tree₁ _) _ tree x₁ s-nil)) 
   = ⟪ (λ eq₁ → bt-ne (trans (sym eq₁) (sym ( just-injective (cong head (just-injective (cong tail eq))) )))) 
     , (λ eq₁ → bt-ne (trans (sym eq₁) (sym ( just-injective (cong head (just-injective (cong tail (just-injective (cong tail eq))) )))) )) ⟫ 
si-property-5 {n} {A} {key} eq (s-right _ _ tree₁ x (s-left .(node _ _ tree₁ _) _ tree x₁ (s-right .(node _ _ (node _ _ tree₁ _) tree) _ tree₂ x₂ si))) 
   = ⟪ (λ eq₁ → bt-ne (trans (sym eq₁) (sym ( just-injective (cong head (just-injective (cong tail eq))) )))) 
     , (λ eq₁ → bt-ne (trans (sym eq₁) (sym ( just-injective (cong head (just-injective (cong tail (just-injective (cong tail eq))) )))) )) ⟫ 
si-property-5 {n} {A} {key} eq (s-right _ _ tree₁ x (s-left .(node _ _ tree₁ _) _ tree x₁ (s-left .(node _ _ (node _ _ tree₁ _) tree) _ tree₂ x₂ si))) 
   = ⟪ (λ eq₁ → bt-ne (trans (sym eq₁) (sym ( just-injective (cong head (just-injective (cong tail eq))) )))) 
     , (λ eq₁ → bt-ne (trans (sym eq₁) (sym ( just-injective (cong head (just-injective (cong tail (just-injective (cong tail eq))) )))) )) ⟫ 
si-property-5 {n} {A} {key} () (s-left _ _ tree x s-nil)
si-property-5 {n} {A} {key} eq (s-left _ _ tree x (s-right .(node _ _ _ tree) _ tree₁ x₁ s-nil)) 
   = ⟪ (λ eq₁ → bt-ne (trans (sym eq₁) (sym ( just-injective (cong head (just-injective (cong tail eq))) )))) 
     , (λ eq₁ → bt-ne (trans (sym eq₁) (sym ( just-injective (cong head (just-injective (cong tail (just-injective (cong tail eq))) )))) )) ⟫ 
si-property-5 {n} {A} {key} eq (s-left _ _ tree x (s-right .(node _ _ _ tree) _ tree₁ x₁ (s-right .(node _ _ tree₁ (node _ _ _ tree)) _ tree₂ x₂ si))) 
   = ⟪ (λ eq₁ → bt-ne (trans (sym eq₁) (sym ( just-injective (cong head (just-injective (cong tail eq))) )))) 
     , (λ eq₁ → bt-ne (trans (sym eq₁) (sym ( just-injective (cong head (just-injective (cong tail (just-injective (cong tail eq))) )))) )) ⟫ 
si-property-5 {n} {A} {key} eq (s-left _ _ tree x (s-right .(node _ _ _ tree) _ tree₁ x₁ (s-left .(node _ _ tree₁ (node _ _ _ tree)) _ tree₂ x₂ si))) 
   = ⟪ (λ eq₁ → bt-ne (trans (sym eq₁) (sym ( just-injective (cong head (just-injective (cong tail eq))) )))) 
     , (λ eq₁ → bt-ne (trans (sym eq₁) (sym ( just-injective (cong head (just-injective (cong tail (just-injective (cong tail eq))) )))) )) ⟫ 
si-property-5 {n} {A} {key} eq (s-left _ _ tree x (s-left .(node _ _ _ tree) _ tree₁ x₁ s-nil)) 
   = ⟪ (λ eq₁ → bt-ne (trans (sym eq₁) (sym ( just-injective (cong head (just-injective (cong tail eq))) )))) 
     , (λ eq₁ → bt-ne (trans (sym eq₁) (sym ( just-injective (cong head (just-injective (cong tail (just-injective (cong tail eq))) )))) )) ⟫ 
si-property-5 {n} {A} {key} eq (s-left _ _ tree x (s-left .(node _ _ _ tree) _ tree₁ x₁ (s-right .(node _ _ (node _ _ _ tree) tree₁) _ tree₂ x₂ si))) 
   = ⟪ (λ eq₁ → bt-ne (trans (sym eq₁) (sym ( just-injective (cong head (just-injective (cong tail eq))) )))) 
     , (λ eq₁ → bt-ne (trans (sym eq₁) (sym ( just-injective (cong head (just-injective (cong tail (just-injective (cong tail eq))) )))) )) ⟫ 
si-property-5 {n} {A} {key} eq (s-left _ _ tree x (s-left .(node _ _ _ tree) _ tree₁ x₁ (s-left .(node _ _ (node _ _ _ tree) tree₁) _ tree₂ x₂ si))) 
   = ⟪ (λ eq₁ → bt-ne (trans (sym eq₁) (sym ( just-injective (cong head (just-injective (cong tail eq))) )))) 
     , (λ eq₁ → bt-ne (trans (sym eq₁) (sym ( just-injective (cong head (just-injective (cong tail (just-injective (cong tail eq))) )))) )) ⟫ 

--
-- if we consider tree invariant, this may be much simpler and faster
--
stackToPG : {n : Level} {A : Set n} → {key : ℕ } → (tree orig : bt A )
           →  (stack : List (bt A)) → stackInvariant key tree orig stack
           → ( stack ≡ orig ∷ [] ) ∨ ( stack ≡ tree ∷ orig ∷ [] ) ∨ PG A key tree stack
stackToPG {n} {A} {key} tree orig [] si = ⊥-elim ( si-property0 si refl )
stackToPG {n} {A} {key} tree orig (x ∷ []) si = case1 (cong (λ k → k ∷ []) (proj1 (si-property-4 tree orig x _ refl si))) 
stackToPG {n} {A} {key} tree orig (x ∷ x₁ ∷ []) si = case2 (case1 (cong₂ (λ j k → j ∷ k ∷ []) si03 si02 )) where
   si02 : x₁ ≡ orig
   si02 = just-injective ( si-property-last _ _ _ _ si )
   si03 : x ≡ tree
   si03 = si-property1 si
stackToPG {n} {A} {key} tree orig (x ∷ x₁ ∷ x₂ ∷ stack) si = case2 (case2 (si01  (x ∷ x₁ ∷ x₂ ∷ stack) stack si refl)) where
   si01 :  (stack stack1 : List (bt A)) → stackInvariant key tree orig stack → stack ≡ (x ∷ x₁ ∷ x₂ ∷ stack1) → PG A key tree stack
   si01 _ _ s-nil ()
   si01 _ _ (s-right tree .(node _ _ tree₁ tree) tree₁ x s-nil) ()
   si01 stack stack1 si@(s-right tree₁ orig tree₂ {key₂} {v2} {st1} lt1 si₁@(s-right .(node _ _ tree₂ tree₁) .orig tree₃ {key₁} {v1} {st} lt2 si₂)) eq 
      with  node→leaf∨IsNode x₂
   ... | case1 geq = ⊥-elim ( proj2 (si-property-5 eq si) geq )
   ... | case2 gn = record {
          parent = x₁ ; uncle = IsNode.left gn ; grand =  x₂
        ; pg = s2-1s2p lt1 (sym si03) (trans (IsNode.t=node gn) (node-cong refl refl refl si04 ) )
        ; rest  = stack1
        ; stack=gp  = cong₂ (λ j k → tree ∷ j ∷ k ) si03 si02
        } where
            si02 : st ≡ x₂ ∷ stack1
            si02 =  ∷-injectiveʳ ( ∷-injectiveʳ eq)
            si03 : node key₂ v2 tree₂ tree₁ ≡ x₁
            si03 = just-injective (cong head (just-injective (cong tail eq)))
            si05 : node key₁ v1 tree₃ (node key₂ v2 tree₂ tree₁) ≡ x₂
            si05 = sym (si-property1 (subst₂ (λ j k → stackInvariant key j orig k) refl si02 si₂))
            si04 : IsNode.right gn ≡ x₁
            si04 = begin
                IsNode.right gn ≡⟨ just-injective (cong node-right ( begin
                    _  ≡⟨ sym (IsNode.t=node gn) ⟩
                    x₂ ≡⟨ sym si05 ⟩
                    node key₁ v1 tree₃ (node key₂ v2 tree₂ tree₁) ≡⟨ cong (λ k →  node key₁ v1 tree₃ k ) si03 ⟩
                    node key₁ v1 tree₃ x₁  ∎ )) ⟩
                x₁ ∎ where open ≡-Reasoning
   si01 _ stack1 si@(s-right tree₃ orig tree₁ {key₂} {v2} lt1 (s-left .(node _ _ tree₁ tree₃) .orig tree₂ {key₁} {v1} {st} lt2 si₂)) eq 
      with  node→leaf∨IsNode x₂
   ... | case1 geq = ⊥-elim ( proj2 (si-property-5 eq si) geq )
   ... | case2 gn = record {
          parent = x₁ ; uncle = IsNode.right gn ; grand =  x₂
        ; pg = s2-1sp2 lt1 (sym si03) (trans (IsNode.t=node gn) (node-cong refl refl si04 refl ) )
        ; rest  = stack1
        ; stack=gp  = cong₂ (λ j k → tree ∷ j ∷ k ) si03 si02
        } where
            si02 : st ≡ x₂ ∷ stack1
            si02 =  ∷-injectiveʳ ( ∷-injectiveʳ eq)
            si03 : node key₂ v2 tree₁ tree₃ ≡ x₁
            si03 = just-injective (cong head (just-injective (cong tail eq)))
            si05 : node key₁ v1  (node key₂ v2 tree₁ tree₃) tree₂ ≡ x₂
            si05 = sym (si-property1 (subst₂ (λ j k → stackInvariant key j orig k) refl si02 si₂ ))
            si04 : IsNode.left gn ≡ x₁
            si04 = begin
                IsNode.left gn ≡⟨ just-injective (cong node-left ( begin
                    _  ≡⟨ sym (IsNode.t=node gn) ⟩
                    x₂ ≡⟨ sym si05 ⟩
                    node key₁ v1  (node key₂ v2  tree₁ tree₃) tree₂ ≡⟨ cong (λ k →  node key₁ v1 k tree₂  ) si03 ⟩
                    node key₁ v1  x₁ tree₂  ∎ )) ⟩
                x₁ ∎ where open ≡-Reasoning
   si01 _ _ (s-left tree₁ .(node _ _ tree₁ tree) tree x s-nil) ()
   si01 _ stack1 si@(s-left tree₃ orig tree₁ {key₂} {v2} lt1 (s-right .(node _ _ tree₃ tree₁) .orig tree₂ {key₁} {v1} {st} lt2 si₂)) eq 
      with  node→leaf∨IsNode x₂
   ... | case1 geq = ⊥-elim ( proj2 (si-property-5 eq si) geq )
   ... | case2 gn = record {
          parent = x₁ ; uncle = IsNode.left gn ; grand =  x₂
        ; pg = s2-s12p lt1 (sym si03) (trans (IsNode.t=node gn) (node-cong refl refl refl si04 ) )
        ; rest  = stack1
        ; stack=gp  = cong₂ (λ j k → tree ∷ j ∷ k ) si03 si02
        } where
            si02 : st ≡ x₂ ∷ stack1
            si02 =  ∷-injectiveʳ ( ∷-injectiveʳ eq)
            si03 : node key₂ v2 tree₃ tree₁ ≡ x₁  
            si03 = just-injective (cong head (just-injective (cong tail eq)))
            si05 : node key₁ v1 tree₂ (node key₂ v2 tree₃ tree₁)  ≡ x₂
            si05 = sym (si-property1 (subst₂ (λ j k → stackInvariant key j orig k) refl si02 si₂ ))
            si04 : IsNode.right gn ≡ x₁
            si04 = begin
                IsNode.right gn ≡⟨ just-injective (cong node-right ( begin
                    _  ≡⟨ sym (IsNode.t=node gn) ⟩
                    x₂ ≡⟨ sym si05 ⟩
                    node key₁ v1 tree₂ _ ≡⟨ cong (λ k →  node key₁ v1 tree₂ k ) si03 ⟩
                    node key₁ v1 tree₂ x₁  ∎ )) ⟩
                x₁ ∎ where open ≡-Reasoning
   si01 _ stack1 si@(s-left tree₃ orig tree₁ {key₂} {v2} lt1 (s-left .(node _ _ tree₃ tree₁) .orig tree₂ {key₁} {v1} {st} lt2 si₂)) eq 
      with  node→leaf∨IsNode x₂
   ... | case1 geq = ⊥-elim ( proj2 (si-property-5 eq si) geq )
   ... | case2 gn = record {
          parent = x₁ ; uncle = IsNode.right gn ; grand =  x₂
        ; pg = s2-s1p2 lt1 (sym si03) (trans (IsNode.t=node gn) (node-cong refl refl si04 refl ) )
        ; rest  = stack1
        ; stack=gp  = cong₂ (λ j k → tree ∷ j ∷ k ) si03 si02
        } where
            si02 : st ≡ x₂ ∷ stack1
            si02 =  ∷-injectiveʳ ( ∷-injectiveʳ eq)
            si03 : node key₂ v2 tree₃ tree₁ ≡ x₁  
            si03 = just-injective (cong head (just-injective (cong tail eq)))
            si05 : node key₁ v1  (node key₂ v2 tree₃ tree₁) tree₂ ≡ x₂
            si05 = sym (si-property1 (subst₂ (λ j k → stackInvariant key j orig k) refl si02 si₂ ))
            si04 : IsNode.left gn ≡ x₁
            si04 = begin
                IsNode.left gn ≡⟨ just-injective (cong node-left ( begin
                    _  ≡⟨ sym (IsNode.t=node gn) ⟩
                    x₂ ≡⟨ sym si05 ⟩
                    node key₁ v1 _ tree₂ ≡⟨ cong (λ k →  node key₁ v1 k tree₂ ) si03 ⟩
                    node key₁ v1 x₁ tree₂  ∎ )) ⟩
                x₁ ∎ where open ≡-Reasoning

stackCase1 : {n : Level} {A : Set n} → {key : ℕ } → {tree orig : bt A }
           →  {stack : List (bt A)} → stackInvariant key tree orig stack
           →  stack ≡ orig ∷ [] → tree ≡ orig
stackCase1 {n} {A} {key} {tree} {.tree} {.(tree ∷ [])} s-nil eq = refl
stackCase1 {n} {A} {key} {tree} {orig} {.(tree ∷ _)} (s-right .tree .orig tree₁ x si) eq = ∷-injectiveˡ eq
stackCase1 {n} {A} {key} {tree} {orig} {.(tree ∷ _)} (s-left .tree .orig tree₁ x si) eq = ∷-injectiveˡ eq

pg-prop-1 : {n : Level} (A : Set n) → (key : ℕ) → (tree orig : bt A )
           →  (stack : List (bt A)) → (pg : PG A key tree stack)
           → (¬  PG.grand pg ≡ leaf ) ∧  (¬  PG.parent pg ≡ leaf)
pg-prop-1 {_} A _ tree orig stack pg with PG.pg pg
... | s2-s1p2 _ refl refl = ⟪ (λ () ) , ( λ () ) ⟫
... | s2-1sp2 _ refl refl = ⟪ (λ () ) , ( λ () ) ⟫
... | s2-s12p _ refl refl = ⟪ (λ () ) , ( λ () ) ⟫
... | s2-1s2p _ refl refl = ⟪ (λ () ) , ( λ () ) ⟫


PGtoRBinvariant1 : {n : Level} {A : Set n}
           → (tree orig : bt (Color ∧ A) )
           → {key : ℕ }
           →  (rb : RBtreeInvariant orig)
           →  (stack : List (bt (Color ∧ A)))  → (si : stackInvariant key tree orig stack )
           →  RBtreeInvariant tree
PGtoRBinvariant1 tree .tree rb .(tree ∷ []) s-nil = rb
PGtoRBinvariant1 {n} {A} tree orig {key} rb (tree ∷ rest) (s-right .tree .orig tree₁ {key₁} {v1} x si) = rb01 ( node key₁ v1 tree₁ tree) refl si  where
    rb01 : (tree₂ : bt (Color ∧ A)) → tree₂ ≡ node key₁ v1 tree₁ tree →  stackInvariant key tree₂ orig rest →  RBtreeInvariant tree
    rb01 tree₂ eq si with PGtoRBinvariant1 _ orig rb _ si
    ... | rb-leaf = ⊥-elim (  bt-ne eq )
    ... | rb-red key value x x₁ x₂ t t₁ = subst (λ k → RBtreeInvariant k) (just-injective (cong node-right eq)) t₁
    ... | rb-black key value x t t₁ = subst (λ k → RBtreeInvariant k) (just-injective (cong node-right eq)) t₁
PGtoRBinvariant1 {n} {A} tree orig {key} rb (tree ∷ rest) (s-left .tree .orig tree₁ {key₁} {v1} x si) = rb01 ( node key₁ v1 tree tree₁) refl si  where
    rb01 : (tree₂ : bt (Color ∧ A)) → tree₂ ≡ node key₁ v1 tree tree₁ →  stackInvariant key tree₂ orig rest →  RBtreeInvariant tree
    rb01 tree₂ eq si with PGtoRBinvariant1 _ orig rb _ si
    ... | rb-leaf = ⊥-elim (  bt-ne eq )
    ... | rb-red key value x x₁ x₂ t t₁ = subst (λ k → RBtreeInvariant k) (just-injective (cong node-left eq)) t
    ... | rb-black key value x t t₁ = subst (λ k → RBtreeInvariant k) (just-injective (cong node-left eq)) t




