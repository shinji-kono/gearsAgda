{-# OPTIONS --cubical-compatible --safe #-}
-- {-# OPTIONS --allow-unsolved-metas --cubical-compatible #-}
module RBTree where

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
open import RBTree1

open _∧_

--
--  findRBT exit with replaced node
--     case-eq        node value is replaced,  just do replacedTree and rebuild rb-invariant
--     case-leaf      insert new single node
--        case1       if parent node is black, just do replacedTree and rebuild rb-invariant
--        case2       if parent node is red,   increase blackdepth, do rotatation
--

findRBT : {n m : Level} {A : Set n} {t : Set m} → (key : ℕ) → (tree tree0 : bt (Color ∧ A) )
           → (stack : List (bt (Color ∧ A)))
           → RBtreeInvariant tree ∧  stackInvariant key tree tree0 stack
           → (next : (tree1 : bt (Color ∧ A) ) → (stack : List (bt (Color ∧ A)))
                   → RBtreeInvariant tree1 ∧ stackInvariant key tree1 tree0 stack
                   → bt-depth tree1 < bt-depth tree → t )
           → (exit : (tree1 : bt (Color ∧ A)) → (stack : List (bt (Color ∧ A)))
                 → RBtreeInvariant tree1 ∧ stackInvariant key tree1 tree0 stack
                 → (tree1 ≡ leaf ) ∨ ( node-key tree1 ≡ just key )  → t ) → t
findRBT key leaf tree0 stack rb0 next exit = exit leaf stack rb0 (case1 refl)
findRBT key (node key₁ value left right) tree0 stack rb0 next exit with <-cmp key key₁
findRBT key (node key₁ value left right) tree0 stack  rb0 next exit | tri< a ¬b ¬c
 = next left (left ∷ stack) ⟪ RBtreeLeftDown left right (_∧_.proj1 rb0) , s-left _ _ _ a (proj2 rb0) ⟫  depth-1<
findRBT key n tree0 stack  rb0 _ exit | tri≈ ¬a refl ¬c = exit n stack rb0 (case2 refl)
findRBT key (node key₁ value left right) tree0 stack  rb0 next exit | tri> ¬a ¬b c
 = next right (right ∷ stack) ⟪ RBtreeRightDown left right (_∧_.proj1 rb0), s-right _ _ _ c (proj2 rb0) ⟫ depth-2<



findTest : {n m : Level} {A : Set n } {t : Set m }
 → (key : ℕ)
 → (tree0 : bt (Color ∧ A))
 → RBtreeInvariant tree0
 → (exit : (tree1 : bt (Color ∧ A))
   → (stack : List (bt (Color ∧ A)))
   → RBtreeInvariant tree1 ∧ stackInvariant key tree1 tree0 stack
   → (tree1 ≡ leaf ) ∨ ( node-key tree1 ≡ just key )  → t ) → t
findTest {n} {m} {A} {t} k tr0 rb0 exit = TerminatingLoopS (bt (Color ∧ A) ∧ List (bt (Color ∧ A)))
 {λ p → RBtreeInvariant (proj1 p) ∧ stackInvariant k (proj1 p) tr0 (proj2 p) } (λ p → bt-depth (proj1 p)) ⟪ tr0 , tr0 ∷ [] ⟫ ⟪ rb0 , s-nil ⟫
       $ λ p RBP loop → findRBT k (proj1 p) tr0 (proj2 p) RBP  (λ t1 s1 P2 lt1 → loop ⟪ t1 ,  s1  ⟫ P2 lt1 )
       $ λ tr1 st P2 O → exit tr1 st P2 O


testRBTree0 :  bt (Color ∧ ℕ)
testRBTree0 = node 8 ⟪ Black , 800 ⟫ (node 5 ⟪ Red , 500 ⟫ (node 2 ⟪ Black , 200 ⟫ leaf leaf) (node 6 ⟪ Black , 600 ⟫ leaf leaf)) (node 10 ⟪ Red , 1000 ⟫ (leaf) (node 15 ⟪ Black , 1500 ⟫ (node 14 ⟪ Red , 1400 ⟫ leaf leaf) leaf))

-- testRBI0 : RBtreeInvariant testRBTree0
-- testRBI0 = rb-node-black (add< 2) (add< 1) refl (rb-node-red (add< 2) (add< 0) refl (rb-single 2 200) (rb-single 6 600)) (rb-right-red (add< 4) refl (rb-left-black (add< 0) refl (rb-single 14 1400) ))

-- findRBTreeTest : result
-- findRBTreeTest = findTest 14 testRBTree0 testRBI0
--        $ λ tr s P O → (record {tree = tr ; stack = s ; ti = (proj1 P) ; si = (proj2 P)})

--
-- create RBT invariant after findRBT, continue to replaceRBT
--
createRBT : {n m : Level} {A : Set n } {t : Set m }
 → (key : ℕ) (value : A)
 → (tree0 : bt (Color ∧ A))
 → RBtreeInvariant tree0
 → treeInvariant tree0
 → (tree1 : bt (Color ∧ A))
 → (stack : List (bt (Color ∧ A)))
 → stackInvariant key tree1 tree0 stack
 → (tree1 ≡ leaf ) ∨ ( node-key tree1 ≡ just key )
 → (exit : (stack : List ( bt (Color ∧ A))) (r : RBI key value tree0 stack ) → t ) → t
createRBT {n} {m} {A} {t} key value orig rbi ti tree [] si P exit = ⊥-elim (si-property0 si refl )
createRBT {n} {m} {A} {t} key value orig rbi ti tree (x ∷ []) si P exit = crbt00 orig P refl where
     crbt00 : (tree1 : bt (Color ∧ A)) → (tree ≡ leaf ) ∨ ( node-key tree ≡ just key ) → tree1 ≡ orig → t
     crbt00 leaf P eq = exit (x ∷ []) record {  
         tree = leaf
         ; repl = node key ⟪ Red , value ⟫ leaf leaf
         ; origti = ti
         ; origrb = rbi
         ; treerb = rb-leaf 
         ; replrb = rb-red key value refl refl refl rb-leaf rb-leaf
         ; replti = t-single key _
         ; si = subst (λ k → stackInvariant key k orig _) crbt01 si
         ; state = rotate leaf refl rbr-leaf
         } where
             crbt01 : tree ≡ leaf
             crbt01 with si-property-last _ _ _ _ si | si-property1 si
             ... | eq3 | eq4 = trans (sym eq4) (trans (just-injective eq3) (sym eq))
     crbt00 (node key₁ value₁ left right ) (case1 eq) eq1 with si-property-last _ _ _ _ si | si-property1 si
     ... | eq2 | eq3 = ⊥-elim (bt-ne (trans (sym eq) (trans (trans (sym eq3) (just-injective eq2) ) (sym eq1) )))
     crbt00 (node key₁ value₁ left right ) (case2 eq) eq1 with si-property-last _ _ _ _ si | si-property1 si
     ... | eq2 | eq3 = exit (x ∷ []) record {  
         tree = node key₁ value₁ left right
         ; repl = node key₁ ⟪ proj1 value₁ , value ⟫ left right 
         ; origti = ti
         ; origrb = rbi
         ; treerb = subst (λ k → RBtreeInvariant k) (sym eq1) rbi
         ; replrb = crbt03 value₁ refl (subst (λ k → RBtreeInvariant k) (sym eq1) rbi)
         ; replti = replaceTree1 _ _ _ (subst (λ k → treeInvariant k) (sym eq1) ti) 
         ; si = subst (λ k → stackInvariant key k orig _) (trans (trans (sym eq3) (just-injective eq2)) (sym eq1)) si
         ; state = rebuild refl (crbt01 value₁ ) (λ ()) crbt04
         }  where 
             crbt01 : (value₁ : Color ∧ A) → black-depth (node key₁ ⟪ proj1 value₁ , value ⟫ left right) ≡ black-depth (node key₁ value₁ left right)
             crbt01 ⟪ Red , proj4 ⟫ = refl
             crbt01 ⟪ Black , proj4 ⟫ = refl
             crbt03 : {tree : bt (Color ∧ A)} → (value₁ : Color ∧ A) → tree ≡ (node key₁ value₁ left right) → RBtreeInvariant tree 
                 →  RBtreeInvariant (node key₁ ⟪ proj1 value₁ , value ⟫ left right)
             crbt03 v1 () rb-leaf
             crbt03 v1 eq (rb-red key₂ value₂ x x₁ x₂ rbi rbi₁) = subst (λ k → RBtreeInvariant k) (node-cong refl (cong (λ k → ⟪ k , _ ⟫ ) 
                (cong proj1 (just-injective (cong node-value eq))) ) 
                (just-injective (cong node-left eq)) (just-injective (cong node-right eq)) ) ( rb-red key₁ value x x₁ x₂ rbi rbi₁ )
             crbt03 v1 eq (rb-black key value x rbi rbi₁) = subst (λ k → RBtreeInvariant k) (node-cong refl (cong (λ k → ⟪ k , _ ⟫ ) 
                (cong proj1 (just-injective (cong node-value eq))) ) 
                (just-injective (cong node-left eq)) (just-injective (cong node-right eq)) ) ( rb-black key₁ _ x rbi rbi₁ )
             crbt04 : replacedRBTree key value (node key₁ value₁ left right) (node key₁ ⟪ proj1 value₁ , value ⟫ left right)
             crbt04 = subst (λ k → replacedRBTree k value (node key₁ value₁ left right) (node key₁ ⟪ proj1 value₁ , value ⟫ left right)) 
                (just-injective (trans (cong node-key (trans eq1 (sym (trans (sym eq3) (just-injective eq2))))) eq) ) rbr-node
createRBT {n} {m} {A} {t} key value orig rbi ti tree (x ∷ leaf ∷ stack) si P exit = ⊥-elim (si-property-parent-node _ _ _ si refl)
createRBT {n} {m} {A} {t} key value orig rbi ti tree sp@(x ∷ node kp vp pleft pright ∷ stack) si P exit = crbt00 tree P refl where
     crbt00 : (tree1 : bt (Color ∧ A)) → (tree ≡ leaf ) ∨ ( node-key tree ≡ just key ) → tree1 ≡ tree → t
     crbt00 leaf P eq = exit sp record {  
         tree = leaf
         ; repl = node key ⟪ Red , value ⟫ leaf leaf
         ; origti = ti
         ; origrb = rbi
         ; treerb = rb-leaf
         ; replrb = rb-red key value refl refl refl rb-leaf rb-leaf
         ; si = subst (λ k → stackInvariant key k orig _) (sym eq) si
         ; replti = t-single key ⟪ Red , value ⟫
         ; state = rotate leaf refl rbr-leaf
         } 
     crbt00 (node key₁ value₁ left right ) (case1 eq) eq1 = ⊥-elim (bt-ne (sym (trans eq1 eq) ))
     crbt00 (node key₁ value₁ left right ) (case2 eq) eq1 with si-property-last _ _ _ _ si | si-property1 si
     ... | eq2 | eq3 = exit sp record {  
         tree = node key₁ value₁ left right
         ; repl = node key₁ ⟪ proj1 value₁ , value ⟫ left right 
         ; origti = ti
         ; origrb = rbi
         ; treerb = treerb
         ; replrb = crbt03 value₁ refl treerb
         ; si = subst (λ k → stackInvariant key k orig _) (sym eq1) si
         ; replti = replaceTree1 _ _ _ (siToTreeinvariant _ _ _ _ ti (subst₂ (λ j k → stackInvariant key j orig k) (sym eq1) (cong (λ k → k ∷ _) 
              (trans eq3 (sym eq1))) si) )
         ; state = rebuild refl (crbt01 value₁ ) (λ ()) crbt04
         }  where 
             crbt01 : (value₁ : Color ∧ A) → black-depth (node key₁ ⟪ proj1 value₁ , value ⟫ left right) ≡ black-depth (node key₁ value₁ left right)
             crbt01 ⟪ Red , proj4 ⟫ = refl
             crbt01 ⟪ Black , proj4 ⟫ = refl
             crbt03 : {tree : bt (Color ∧ A) } (value₁ : Color ∧ A) → tree ≡ node key₁ value₁ left right →  RBtreeInvariant tree
                → RBtreeInvariant (node key₁ ⟪ proj1 value₁ , value ⟫ left right)
             crbt03 _ () rb-leaf
             crbt03 ⟪ Red , proj4 ⟫ teq (rb-red key₂ proj5 x x₁ x₂ rbi rbi₁) = subst (λ k → RBtreeInvariant k) (node-cong refl (cong (λ k → ⟪ k , value ⟫ ) 
                (cong proj1 (just-injective (cong node-value teq))) ) 
                (just-injective (cong node-left teq)) (just-injective (cong node-right teq)) ) ( rb-red key₁ value x x₁ x₂ rbi rbi₁ )
             crbt03 ⟪ Black , proj4 ⟫ () (rb-red key₁ proj5 x x₁ x₂ rbi rbi₁)
             crbt03 ⟪ Black , proj4 ⟫ teq (rb-black key₂ proj5 x rbi rbi₁) = subst (λ k → RBtreeInvariant k) (node-cong refl (cong (λ k → ⟪ k , value ⟫ ) 
                (cong proj1 (just-injective (cong node-value teq))) ) 
                (just-injective (cong node-left teq)) (just-injective (cong node-right teq)) ) ( rb-black key₁ _ x rbi rbi₁ )
             crbt03 ⟪ Red , proj4 ⟫ () (rb-black key₁ proj5 x rbi rbi₁)
             keq : key₁ ≡ key
             keq = just-injective (trans (cong node-key eq1) eq)
             crbt04 : replacedRBTree key value (node key₁ value₁ left right) (node key₁ ⟪ proj1 value₁ , value ⟫ left right)
             crbt04 = subst (λ k → replacedRBTree k value (node key₁ value₁ left right) (node key₁ ⟪ proj1 value₁ , value ⟫ left right)) keq rbr-node
             treerb : RBtreeInvariant (node key₁ value₁ left right)
             treerb = PGtoRBinvariant1 _ orig rbi _ (subst (λ k → stackInvariant key k orig _) (sym eq1) si)


ti-to-black : {n : Level} {A : Set n} → {tree : bt (Color ∧ A)} → treeInvariant tree → treeInvariant (to-black tree)
ti-to-black {n} {A} {.leaf} t-leaf = t-leaf
ti-to-black {n} {A} {.(node key value leaf leaf)} (t-single key value) = t-single key ⟪ Black , proj2 value ⟫
ti-to-black {n} {A} {.(node key _ leaf (node key₁ _ _ _))} (t-right key key₁ x x₁ x₂ ti) = t-right key key₁ x x₁ x₂ ti
ti-to-black {n} {A} {.(node key₁ _ (node key _ _ _) leaf)} (t-left key key₁ x x₁ x₂ ti) = t-left key key₁ x x₁ x₂ ti
ti-to-black {n} {A} {.(node key₁ _ (node key _ _ _) (node key₂ _ _ _))} (t-node key key₁ key₂ x x₁ x₂ x₃ x₄ x₅ ti ti₁) = t-node key key₁ key₂ x x₁ x₂ x₃ x₄ x₅ ti ti₁

--
--   rotate and rebuild replaceTree and rb-invariant
--
replaceRBP : {n m : Level} {A : Set n} {t : Set m}
     → (key : ℕ) → (value : A)
     → (orig : bt (Color ∧ A))
     → (stack : List (bt (Color ∧ A)))
     → (r : RBI key value orig stack )
     → (next :  (stack1 : List (bt (Color ∧ A)))
        → (r : RBI key value orig stack1 )
        → length stack1 < length stack  → t )
     → (exit : (stack1 : List (bt (Color ∧ A)))
        →  stack1 ≡ (orig ∷ [])
        →  RBI key value orig stack1
        → t ) → t
replaceRBP {n} {m} {A} {t} key value orig stack r next exit = replaceRBP1 where
    -- we have no grand parent
    -- eq : stack₁ ≡ RBI.tree r ∷ orig ∷ []
    -- change parent color ≡ Black and exit
    -- one level stack, orig is parent of repl
    repl = RBI.repl r
    insertCase4 :  (tr0 : bt (Color ∧ A)) → tr0 ≡ orig
       → (eq : stack ≡ RBI.tree r ∷ orig ∷ [])
       → (rot : replacedRBTree key value (RBI.tree r) repl)
       → ( color repl ≡ Red ) ∨ (color (RBI.tree r) ≡ color repl)
       → stackInvariant key (RBI.tree r) orig stack
       → t
    insertCase4 leaf eq1 eq rot col si = ⊥-elim (rb04 eq eq1 si) where -- can't happen
       rb04 : {stack : List ( bt ( Color ∧ A))} → stack ≡ RBI.tree r ∷ orig ∷ [] → leaf ≡ orig → stackInvariant key (RBI.tree r) orig stack →   ⊥
       rb04 () eq1 s-nil
       rb04 eq eq1 (s-right .(RBI.tree r) .orig tree₁ x si) =  si-property2 _ (s-right _ _ tree₁ x si) (trans (cong just eq1) 
           (sym (cong stack-last (∷-injectiveʳ eq))))
       rb04 eq eq1 (s-left .(RBI.tree r) .orig tree x si) =  si-property2 _ (s-left _ _ tree x si) (trans (cong just eq1) 
           (sym (cong stack-last (∷-injectiveʳ eq))))
    insertCase4  tr0@(node key₁ value₁ left right) refl eq rot col si with <-cmp key key₁
    ... | tri< a ¬b ¬c = rb07 col where
       rb04 : stackInvariant key (RBI.tree r) orig stack → stack ≡ RBI.tree r ∷ orig ∷ [] → tr0 ≡ orig → left ≡ RBI.tree r
       rb04 s-nil () eq1
       rb04 (s-right tree .(node key₁ value₁ left right) tree₁ {key₂} {v1} {st} x si₁) eq eq1 = 
               ⊥-elim ( nat-<> x (subst (λ k → key < k) (rb10 (subst (λ k → stackInvariant _ _ _ k ) rb11 si₁)) a )) where
           rb11 : st ≡ node key₁ value₁ left right ∷ []
           rb11 = ∷-injectiveʳ eq
           rb10 :  stackInvariant key (node key₂ v1 tree₁ tree) (node key₁ value₁ left right) (node key₁ value₁ left right ∷ []) → key₁ ≡ key₂
           rb10 si₁ = just-injective (cong node-key (si-property1 si₁))
       rb04 (s-left tree₁ .(node key₁ value₁ left right) tree {key₂} {v1} {st} x si₁) eq eq1 = 
              rb10 (subst (λ k → stackInvariant _ _ _ k ) rb11 si₁) where
           rb11 : st ≡ node key₁ value₁ left right ∷ []
           rb11 = ∷-injectiveʳ eq
           rb10 :  stackInvariant key (node key₂ v1 tree₁ tree) (node key₁ value₁ left right) (node key₁ value₁ left right ∷ []) → left ≡ tree₁ 
           rb10 si₁ = just-injective (cong node-left (si-property1 si₁))
       rb06 : black-depth repl ≡ black-depth right
       rb06 = begin
         black-depth repl ≡⟨ sym (RB-repl→eq _ _ (RBI.treerb r) rot) ⟩
         black-depth (RBI.tree r) ≡⟨ cong black-depth (sym (rb04 si eq refl)) ⟩
         black-depth left ≡⟨ (RBtreeEQ (RBI.origrb r)) ⟩
         black-depth right ∎
            where open ≡-Reasoning
       rb08 :  (color (RBI.tree r) ≡ color repl) → RBtreeInvariant (node key₁ value₁ repl right)
       rb08 ceq with proj1 value₁ in coeq
       ... | Red = subst (λ k → RBtreeInvariant (node key₁ k repl right)) (cong (λ k → ⟪ k , _ ⟫) (sym coeq) )
           (rb-red _ (proj2 value₁) rb09 (proj2 (RBtreeChildrenColorBlack _ _ (RBI.origrb r) coeq)) rb06 (RBI.replrb r)
               (RBtreeRightDown _ _ (RBI.origrb r))) where
           rb09 : color repl ≡ Black
           rb09 = trans (trans (sym ceq) (sym (cong color (rb04 si eq refl) ))) (proj1 (RBtreeChildrenColorBlack _ _ (RBI.origrb r) coeq))
       ... | Black = subst (λ k → RBtreeInvariant (node key₁ k repl right)) (cong (λ k → ⟪ k , _ ⟫) (sym coeq) )
           (rb-black _ (proj2 value₁) rb06 (RBI.replrb r) (RBtreeRightDown _ _ (RBI.origrb r)))
       rb07 : ( color repl ≡ Red ) ∨ (color (RBI.tree r) ≡ color repl) → t
       rb07 (case2 cc ) = exit  (orig ∷ []) refl record {
         tree = orig
         ; repl = node key₁ value₁ repl right
         ; origti = RBI.origti r
         ; origrb = RBI.origrb r
         ; treerb = RBI.origrb r
         ; replrb = rb08 cc
         ; replti = RB-repl→ti _ _ _ _ (RBI.origti r) rb10
         ; si = s-nil
         ; state = top-black  refl (case1 rb10 )
         } where
             rb10 : replacedRBTree key value (node key₁ value₁ left right) (node key₁ value₁ repl right)
             rb10 = rbr-left (trans (cong color (rb04 si eq refl)) cc) a (subst (λ k → replacedRBTree key value k repl) (sym (rb04 si eq refl)) rot)
       rb07 (case1 repl-red) = exit  (orig ∷ []) refl record {
         tree = orig
         ; repl = to-black (node key₁ value₁ repl right)
         ; origti = RBI.origti r
         ; origrb = RBI.origrb r
         ; treerb = RBI.origrb r
         ; replrb = rb-black _ _ rb06 (RBI.replrb r) (RBtreeRightDown _ _ (RBI.origrb r))
         ; replti = RB-repl→ti _ _ _ _ (ti-to-black (RBI.origti r)) rb10
         ; si = s-nil
         ; state = top-black  refl (case2 rb10 )
         } where
              rb10 : replacedRBTree key value (node key₁ ⟪ Black , proj2 value₁ ⟫ left right) (node key₁ ⟪ Black , proj2 value₁ ⟫ repl right)
              rb10 = rbr-black-left repl-red a (subst (λ k → replacedRBTree key value k repl) (sym (rb04 si eq refl)) rot)
    ... | tri≈ ¬a b ¬c = ⊥-elim ( si-property-pne _ _ stack eq si b ) -- can't happen
    ... | tri> ¬a ¬b c = rb07 col where
       rb04 : stackInvariant key (RBI.tree r) orig stack → stack ≡ RBI.tree r ∷ orig ∷ [] → tr0 ≡ orig → right ≡ RBI.tree r
       rb04 s-nil () eq1
       rb04 (s-left tree .(node key₁ value₁ left right) tree₁ {key₂} {v1} {st} x si₁) eq eq1 = 
               ⊥-elim ( nat-<> x (subst (λ k → k < key ) (rb10 (subst (λ k → stackInvariant _ _ _ k ) rb11 si₁)) c )) where
           rb11 : st ≡ node key₁ value₁ left right ∷ []
           rb11 = ∷-injectiveʳ eq
           rb10 :  stackInvariant key (node key₂ v1 tree tree₁) (node key₁ value₁ left right) (node key₁ value₁ left right ∷ []) → key₁ ≡ key₂
           rb10 si₁ = just-injective (cong node-key (si-property1 si₁))
       rb04 (s-right tree₁ .(node key₁ value₁ left right) tree {key₂} {v1} {st} x si₁) eq eq1 = 
              rb10 (subst (λ k → stackInvariant _ _ _ k ) rb11 si₁) where
           rb11 : st ≡ node key₁ value₁ left right ∷ []
           rb11 = ∷-injectiveʳ eq
           rb10 :  stackInvariant key (node key₂ v1 tree tree₁) (node key₁ value₁ left right) (node key₁ value₁ left right ∷ []) → right ≡ tree₁
           rb10 si₁ = just-injective (cong node-right (si-property1 si₁))
       rb06 : black-depth repl ≡ black-depth left
       rb06 = begin
         black-depth repl ≡⟨ sym (RB-repl→eq _ _ (RBI.treerb r) rot) ⟩
         black-depth (RBI.tree r) ≡⟨ cong black-depth (sym (rb04 si eq refl)) ⟩
         black-depth right ≡⟨ (sym (RBtreeEQ (RBI.origrb r))) ⟩
         black-depth left ∎
            where open ≡-Reasoning
       rb08 :  (color (RBI.tree r) ≡ color repl) → RBtreeInvariant (node key₁ value₁ left repl )
       rb08 ceq with proj1 value₁ in coeq
       ... | Red = subst (λ k → RBtreeInvariant (node key₁ k left repl )) (cong (λ k → ⟪ k , _ ⟫) (sym coeq) )
           (rb-red _ (proj2 value₁) (proj1 (RBtreeChildrenColorBlack _ _ (RBI.origrb r) coeq)) rb09 (sym rb06)
               (RBtreeLeftDown _ _ (RBI.origrb r))(RBI.replrb r)) where
           rb09 : color repl ≡ Black
           rb09 = trans (trans (sym ceq) (sym (cong color (rb04 si eq refl) ))) (proj2 (RBtreeChildrenColorBlack _ _ (RBI.origrb r) coeq))
       ... | Black = subst (λ k → RBtreeInvariant (node key₁ k left repl )) (cong (λ k → ⟪ k , _ ⟫) (sym coeq) )
           (rb-black _ (proj2 value₁) (sym rb06)  (RBtreeLeftDown _ _ (RBI.origrb r)) (RBI.replrb r))
       rb07 : ( color repl ≡ Red ) ∨ (color (RBI.tree r) ≡ color repl) → t
       rb07 (case2 cc ) = exit  (orig ∷ []) refl record {
         tree = orig
         ; repl = node key₁ value₁ left repl
         ; origti = RBI.origti r
         ; origrb = RBI.origrb r
         ; treerb = RBI.origrb r
         ; replrb = rb08 cc
         ; replti = RB-repl→ti _ _ _ _ (RBI.origti r) rb10
         ; si = s-nil
         ; state = top-black  refl (case1 rb10)
         } where
             rb10 = rbr-right (trans (cong color (rb04 si eq refl)) cc) c (subst (λ k → replacedRBTree key value k repl) (sym (rb04 si eq refl)) rot)
       rb07 (case1 repl-red ) = exit  (orig ∷ [])  refl record {
         tree = orig
         ; repl = to-black (node key₁ value₁ left repl)
         ; origti = RBI.origti r
         ; origrb = RBI.origrb r
         ; treerb = RBI.origrb r
         ; replrb = rb-black _ _ (sym rb06) (RBtreeLeftDown _ _ (RBI.origrb r)) (RBI.replrb r)
         ; replti = RB-repl→ti _ _ _ _ (ti-to-black (RBI.origti r)) rb10
         ; si = s-nil
         ; state = top-black refl (case2 rb10 )
         } where
            rb10 = rbr-black-right repl-red c (subst (λ k → replacedRBTree key value k repl) (sym (rb04 si eq refl)) rot)
    rebuildCase : (ceq : color (RBI.tree r) ≡ color repl)
       → (bdepth-eq : black-depth repl ≡ black-depth (RBI.tree r))
       → (¬ RBI.tree r ≡ leaf)
       → (rot       : replacedRBTree key value (RBI.tree r) repl ) → t
    rebuildCase ceq bdepth-eq ¬leaf rot with stackToPG (RBI.tree r) orig stack (RBI.si r)
    ... | case1 x = exit stack x r  where  -- single node case
        rb00 : stack ≡ orig ∷ [] → orig ≡ RBI.tree r
        rb00 refl = si-property1 (RBI.si r)
    ... | case2 (case1 x) = insertCase4 orig refl x rot (case2 ceq) (RBI.si r)   -- one level stack, orig is parent of repl
    ... | case2 (case2 pg) = rebuildCase1 pg where
       rb00 : (pg : PG (Color ∧ A) key (RBI.tree r) stack) → stackInvariant key (RBI.tree r) orig (RBI.tree r ∷ PG.parent pg ∷ PG.grand pg ∷ PG.rest pg)
       rb00 pg = subst (λ k → stackInvariant key (RBI.tree r) orig k) (PG.stack=gp pg) (RBI.si r)
       treerb : (pg : PG (Color ∧ A) key (RBI.tree r) stack) → RBtreeInvariant (PG.parent pg)
       treerb pg = PGtoRBinvariant1 _ orig (RBI.origrb r) _ (popStackInvariant _ _ _ _ _ (rb00 pg))
       rb08 : (pg : PG (Color ∧ A) key (RBI.tree r) stack) → treeInvariant (PG.parent pg)
       rb08 pg = siToTreeinvariant _ _ _ _ (RBI.origti r) (popStackInvariant _ _ _ _ _ (rb00 pg))
       rebuildCase1 : (PG (Color ∧ A) key (RBI.tree r) stack) → t
       rebuildCase1 pg with PG.pg pg
       ... | s2-s1p2 {kp} {kg} {vp} {vg} {n1} {n2} lt lt2 x x₁ = rebuildCase2 where
          rebuildCase2 : t
          rebuildCase2 = next (PG.parent pg ∷ PG.grand pg ∷ PG.rest pg) record {
              tree = PG.parent pg
              ; repl = rb01
              ; origti = RBI.origti r
              ; origrb = RBI.origrb r
              ; treerb = treerb pg
              ; replrb = rb02 (PG.parent pg) x (treerb pg)
              ; replti = RB-repl→ti _ _ _ _ (rb08 pg) (subst (λ k → replacedRBTree key value k rb01) (sym x) (rbr-left ceq rb04 rot))
              ; si = popStackInvariant _ _ _ _ _ (rb00 pg)
              ; state = rebuild (cong color x) rb06 (subst (λ k → ¬ (k ≡ leaf)) (sym x) (λ ()))  (subst (λ k → replacedRBTree key value k rb01) (sym x) (rbr-left ceq rb04 rot))
             } (subst₂ (λ j k → j < length k ) refl (sym (PG.stack=gp pg)) ≤-refl) where
               rb01 : bt (Color ∧ A)
               rb01 = node kp vp repl n1
               rb03 : black-depth n1 ≡ black-depth repl
               rb03 = trans (sym (RBtreeEQ (subst (λ k → RBtreeInvariant k) x (treerb pg)))) (RB-repl→eq _ _ (RBI.treerb r) rot)
               rb02 : (tree : bt (Color ∧ A)) → tree ≡ node kp vp (RBI.tree r) n1 →  RBtreeInvariant tree → RBtreeInvariant rb01
               rb02 .leaf eq rb-leaf = ⊥-elim ( bt-ne eq )
               rb02 (node key ⟪ Red , value ⟫ left right) eq (rb-red key value cx cx₁ x₂ rbi rbi₁) = 
                   subst (λ k → RBtreeInvariant k) (node-cong refl rb11 refl rb12) (rb-red kp value (trans (sym ceq) rb13) cx₁ rb14 (RBI.replrb r) rbi₁) where
                     rb11 : ⟪ Red , value ⟫ ≡ vp
                     rb11 = just-injective (cong node-value eq)
                     rb12 : right ≡ n1
                     rb12 = just-injective (cong node-right eq)
                     rb13 : color (RBI.tree r) ≡ Black 
                     rb13 = trans (sym (cong color ( just-injective (cong node-left eq) ))) cx
                     rb14 : black-depth repl ≡ black-depth right
                     rb14 = trans (sym rb03) (cong black-depth (sym (just-injective (cong node-right eq))))
               rb02 (node key ⟪ Black , value ⟫ left right) eq (rb-black key value cx rbi rbi₁) = 
                   subst (λ k → RBtreeInvariant k) (node-cong refl rb11 refl rb12) (rb-black kp value rb14 (RBI.replrb r) rbi₁) where
                     rb11 : ⟪ Black , value ⟫ ≡ vp
                     rb11 = just-injective (cong node-value eq)
                     rb12 : right ≡ n1
                     rb12 = just-injective (cong node-right eq)
                     rb14 : black-depth repl ≡ black-depth right
                     rb14 = trans (sym rb03) (cong black-depth (sym (just-injective (cong node-right eq))))
               rb05 : treeInvariant (node kp vp (RBI.tree r) n1 )
               rb05 = subst (λ k → treeInvariant k) x (rb08 pg)
               rb04 : key < kp
               rb04 = lt
               rb06 : black-depth rb01 ≡ black-depth (PG.parent pg)
               rb06 = trans (rb07 vp) ( cong black-depth (sym x) ) where
                   rb07 : (vp : Color ∧ A) → black-depth (node kp vp repl n1) ≡ black-depth (node kp vp (RBI.tree r) n1 )
                   rb07 ⟪ Black  , proj4 ⟫ = cong (λ k → suc (k ⊔ black-depth n1 )) bdepth-eq
                   rb07 ⟪ Red  , proj4 ⟫ = cong (λ k → (k ⊔ black-depth n1  )) bdepth-eq
       ... | s2-1sp2 {kp} {kg} {vp} {vg} {n1} {n2} lt lt2 x x₁ = rebuildCase2 where
          rebuildCase2 : t
          rebuildCase2 = next (PG.parent pg ∷ PG.grand pg ∷ PG.rest pg) record {
              tree = PG.parent pg
              ; repl = rb01
              ; origti = RBI.origti r
              ; origrb = RBI.origrb r
              ; treerb = treerb pg
              ; replrb = rb02 (PG.parent pg) x (treerb pg)
              ; replti = RB-repl→ti _ _ _ _ (rb08 pg) (subst (λ k → replacedRBTree key value k rb01) (sym x) (rbr-right ceq rb04 rot))
              ; si = popStackInvariant _ _ _ _ _ (rb00 pg)
              ; state = rebuild (cong color x) rb06 (subst (λ k → ¬ (k ≡ leaf)) (sym x) (λ ())) (subst (λ k → replacedRBTree key value k rb01) (sym x) (rbr-right ceq rb04 rot))
             } (subst₂ (λ j k → j < length k ) refl (sym (PG.stack=gp pg)) ≤-refl) where
               rb01 : bt (Color ∧ A)
               rb01 = node kp vp n1 repl
               rb03 : black-depth n1 ≡ black-depth repl
               rb03 = trans (RBtreeEQ (subst (λ k → RBtreeInvariant k) x (treerb pg))) ((RB-repl→eq _ _ (RBI.treerb r) rot))
               rb02 : (tree : bt (Color ∧ A)) → tree ≡ node kp vp n1 (RBI.tree r) →  RBtreeInvariant tree → RBtreeInvariant rb01
               rb02 .leaf eq rb-leaf = ⊥-elim ( bt-ne eq )
               rb02 (node key ⟪ Red , value ⟫ left right) eq (rb-red key value cx cx₁ x₂ rbi rbi₁) = 
                   subst (λ k → RBtreeInvariant k) (node-cong refl rb11 rb12 refl) (rb-red kp value cx (trans (sym ceq) rb13) (sym rb14) rbi (RBI.replrb r)) where
                     rb11 : ⟪ Red , value ⟫ ≡ vp
                     rb11 = just-injective (cong node-value eq)
                     rb12 : left ≡ n1
                     rb12 = just-injective (cong node-left eq)
                     rb13 : color (RBI.tree r) ≡ Black 
                     rb13 = trans (sym (cong color ( just-injective (cong node-right eq) ))) cx₁
                     rb14 : black-depth repl ≡ black-depth left
                     rb14 = trans (sym rb03) (cong black-depth (sym (just-injective (cong node-left eq))))
               rb02 (node key ⟪ Black , value ⟫ left right) eq (rb-black key value cx rbi rbi₁) = 
                   subst (λ k → RBtreeInvariant k) (node-cong refl rb11 rb12 refl) (rb-black kp value (sym rb14) rbi (RBI.replrb r)) where
                     rb11 : ⟪ Black , value ⟫ ≡ vp
                     rb11 = just-injective (cong node-value eq)
                     rb12 : left ≡ n1
                     rb12 = just-injective (cong node-left eq)
                     rb14 : black-depth repl ≡ black-depth left
                     rb14 = trans (sym rb03) (cong black-depth (sym (just-injective (cong node-left eq))))
               rb05 : treeInvariant (node kp vp n1 (RBI.tree r) )
               rb05 = subst (λ k → treeInvariant k) x (rb08 pg)
               rb04 : kp < key
               rb04 = lt
               rb06 : black-depth rb01 ≡ black-depth (PG.parent pg)
               rb06 = trans (rb07 vp) ( cong black-depth (sym x) ) where
                   rb07 : (vp : Color ∧ A) → black-depth (node kp vp n1 repl) ≡ black-depth (node kp vp n1 (RBI.tree r))
                   rb07 ⟪ Black  , proj4 ⟫ = cong (λ k → suc (black-depth n1 ⊔ k)) bdepth-eq
                   rb07 ⟪ Red  , proj4 ⟫ = cong (λ k → (black-depth n1 ⊔ k)) bdepth-eq
       ... | s2-s12p {kp} {kg} {vp} {vg} {n1} {n2} lt lt2 x x₁ = rebuildCase2 where
          rebuildCase2 : t
          rebuildCase2 = next (PG.parent pg ∷ PG.grand pg ∷ PG.rest pg) record {
              tree = PG.parent pg
              ; repl = rb01
              ; origti = RBI.origti r
              ; origrb = RBI.origrb r
              ; treerb = treerb pg
              ; replrb = rb02 (PG.parent pg) x (treerb pg)
              ; replti = RB-repl→ti _ _ _ _ (rb08 pg) (subst (λ k → replacedRBTree key value k rb01) (sym x) (rbr-left ceq rb04 rot))
              ; si = popStackInvariant _ _ _ _ _ (rb00 pg)
              ; state = rebuild (cong color x) rb06 (subst (λ k → ¬ (k ≡ leaf)) (sym x) (λ ())) (subst (λ k → replacedRBTree key value k rb01) (sym x) (rbr-left ceq rb04 rot))
             } (subst₂ (λ j k → j < length k ) refl (sym (PG.stack=gp pg)) ≤-refl) where
               rb01 : bt (Color ∧ A)
               rb01 = node kp vp repl n1
               rb03 : black-depth n1 ≡ black-depth repl
               rb03 = trans (sym (RBtreeEQ (subst (λ k → RBtreeInvariant k) x (treerb pg)))) ((RB-repl→eq _ _ (RBI.treerb r) rot))
               rb02 : (tree : bt (Color ∧ A)) → tree ≡ node kp vp (RBI.tree r) n1 →  RBtreeInvariant tree → RBtreeInvariant rb01
               rb02 .leaf eq rb-leaf = ⊥-elim ( bt-ne eq )
               rb02 (node key ⟪ Red , value ⟫ left right) eq (rb-red key value cx cx₁ x₂ rbi rbi₁) = 
                   subst (λ k → RBtreeInvariant k) (node-cong refl rb11 refl rb12) (rb-red kp value (trans (sym ceq) rb13) cx₁ rb14 (RBI.replrb r) rbi₁) where
                     rb11 : ⟪ Red , value ⟫ ≡ vp
                     rb11 = just-injective (cong node-value eq)
                     rb12 : right ≡ n1
                     rb12 = just-injective (cong node-right eq)
                     rb13 : color (RBI.tree r) ≡ Black 
                     rb13 = trans (sym (cong color ( just-injective (cong node-left eq) ))) cx
                     rb14 : black-depth repl ≡ black-depth right
                     rb14 = trans (sym rb03) (cong black-depth (sym (just-injective (cong node-right eq))))
               rb02 (node key ⟪ Black , value ⟫ left right) eq (rb-black key value cx rbi rbi₁) = 
                   subst (λ k → RBtreeInvariant k) (node-cong refl rb11 refl rb12) (rb-black kp value rb14 (RBI.replrb r) rbi₁) where
                     rb11 : ⟪ Black , value ⟫ ≡ vp
                     rb11 = just-injective (cong node-value eq)
                     rb12 : right ≡ n1
                     rb12 = just-injective (cong node-right eq)
                     rb14 : black-depth repl ≡ black-depth right
                     rb14 = trans (sym rb03) (cong black-depth (sym (just-injective (cong node-right eq))))
               rb05 : treeInvariant (node kp vp (RBI.tree r) n1)
               rb05 = subst (λ k → treeInvariant k) x (rb08 pg)
               rb04 : key < kp
               rb04 = lt
               rb06 : black-depth rb01 ≡ black-depth (PG.parent pg)
               rb06 = trans (rb07 vp) ( cong black-depth (sym x) ) where
                   rb07 : (vp : Color ∧ A) → black-depth (node kp vp repl n1) ≡ black-depth (node kp vp (RBI.tree r) n1)
                   rb07 ⟪ Black  , proj4 ⟫ = cong (λ k → suc (k ⊔ black-depth n1 )) bdepth-eq
                   rb07 ⟪ Red  , proj4 ⟫ = cong (λ k → (k ⊔ black-depth n1 ))  bdepth-eq
       ... | s2-1s2p {kp} {kg} {vp} {vg} {n1} {n2} lt lt2 x x₁ = rebuildCase2 where
          rebuildCase2 : t
          rebuildCase2 = next (PG.parent pg ∷ PG.grand pg ∷ PG.rest pg) record {
              tree = PG.parent pg
              ; repl = rb01
              ; origti = RBI.origti r
              ; origrb = RBI.origrb r
              ; treerb = treerb pg
              ; replrb = rb02 (PG.parent pg) x (treerb pg)
              ; replti = RB-repl→ti _ _ _ _ (rb08 pg) (subst (λ k → replacedRBTree key value k rb01) (sym x) (rbr-right ceq rb04 rot))
              ; si = popStackInvariant _ _ _ _ _ (rb00 pg)
              ; state = rebuild (cong color x) rb06 (subst (λ k → ¬ (k ≡ leaf)) (sym x) (λ ())) (subst (λ k → replacedRBTree key value k rb01) (sym x) (rbr-right ceq rb04 rot))
             } (subst₂ (λ j k → j < length k ) refl (sym (PG.stack=gp pg)) ≤-refl) where
               rb01 : bt (Color ∧ A)
               rb01 = node kp vp n1 repl
               rb03 : black-depth n1 ≡ black-depth repl
               rb03 = trans (RBtreeEQ (subst (λ k → RBtreeInvariant k) x (treerb pg))) ((RB-repl→eq _ _ (RBI.treerb r) rot))
               rb02 : (tree : bt (Color ∧ A)) → tree ≡ node kp vp n1 (RBI.tree r) →  RBtreeInvariant tree → RBtreeInvariant rb01
               rb02 .leaf eq rb-leaf = ⊥-elim ( bt-ne eq )
               rb02 (node key ⟪ Red , value ⟫ left right) eq (rb-red key value cx cx₁ x₂ rbi rbi₁) = 
                   subst (λ k → RBtreeInvariant k) (node-cong refl rb11 rb12 refl) (rb-red kp value cx (trans (sym ceq) rb13) (sym rb14) rbi (RBI.replrb r)) where
                     rb11 : ⟪ Red , value ⟫ ≡ vp
                     rb11 = just-injective (cong node-value eq)
                     rb12 : left ≡ n1
                     rb12 = just-injective (cong node-left eq)
                     rb13 : color (RBI.tree r) ≡ Black 
                     rb13 = trans (sym (cong color ( just-injective (cong node-right eq) ))) cx₁
                     rb14 : black-depth repl ≡ black-depth left
                     rb14 = trans (sym rb03) (cong black-depth (sym (just-injective (cong node-left eq))))
               rb02 (node key ⟪ Black , value ⟫ left right) eq (rb-black key value cx rbi rbi₁) = 
                   subst (λ k → RBtreeInvariant k) (node-cong refl rb11 rb12 refl) (rb-black kp value (sym rb14) rbi (RBI.replrb r)) where
                     rb11 : ⟪ Black , value ⟫ ≡ vp
                     rb11 = just-injective (cong node-value eq)
                     rb12 : left ≡ n1
                     rb12 = just-injective (cong node-left eq)
                     rb14 : black-depth repl ≡ black-depth left
                     rb14 = trans (sym rb03) (cong black-depth (sym (just-injective (cong node-left eq))))
               rb05 : treeInvariant (node kp vp n1 (RBI.tree r))
               rb05 = subst (λ k → treeInvariant k) x (rb08 pg)
               rb04 : kp < key
               rb04 = si-property-> ¬leaf rb05 (subst (λ k → stackInvariant key (RBI.tree r) orig (RBI.tree r ∷ k ∷ PG.grand pg ∷ PG.rest pg)) x (rb00 pg))
               rb06 : black-depth rb01 ≡ black-depth (PG.parent pg)
               rb06 = trans (rb07 vp) ( cong black-depth (sym x) ) where
                   rb07 : (vp : Color ∧ A) → black-depth (node kp vp n1 repl) ≡ black-depth (node kp vp n1 (RBI.tree r))
                   rb07 ⟪ Black  , proj4 ⟫ = cong (λ k → suc (black-depth n1 ⊔ k)) bdepth-eq
                   rb07 ⟪ Red  , proj4 ⟫ = cong (λ k → (black-depth n1 ⊔ k)) bdepth-eq
    --
    -- both parent and uncle are Red, rotate then goto rebuild
    --
    insertCase5 : (repl1 : bt (Color ∧ A)) → repl1 ≡ repl
       → (pg : PG (Color ∧ A) key (RBI.tree r) stack)
       → (rot : replacedRBTree key value (RBI.tree r) repl)
       → color repl ≡ Red → color (PG.uncle pg) ≡ Black → color (PG.parent pg) ≡ Red → t
    insertCase5 leaf eq pg rot repl-red uncle-black pcolor = ⊥-elim ( rb00 repl repl-red (cong color (sym eq))) where
        rb00 : (repl : bt (Color ∧ A)) → color repl ≡ Red → color repl ≡ Black → ⊥
        rb00 repl eq eq₁ = ⊥-elim ( ⊥-color (trans (sym eq₁) eq ))
    insertCase5 (node rkey vr rp-left rp-right) eq pg rot repl-red uncle-black pcolor = insertCase51 where
        rb00 : stackInvariant key (RBI.tree r) orig (RBI.tree r ∷ PG.parent pg ∷ PG.grand pg ∷ PG.rest pg)
        rb00 = subst (λ k → stackInvariant key (RBI.tree r) orig k) (PG.stack=gp pg) (RBI.si r)
        rb15 : suc (length (PG.rest pg)) < length stack
        rb15 = begin
              suc (suc (length (PG.rest pg))) ≤⟨ <-trans (n<1+n _) (n<1+n _) ⟩
              length (RBI.tree r ∷ PG.parent pg ∷ PG.grand pg ∷ PG.rest pg) ≡⟨ cong length (sym (PG.stack=gp pg)) ⟩
              length stack ∎
                 where open ≤-Reasoning
        rb02 : RBtreeInvariant (PG.grand pg)
        rb02 = PGtoRBinvariant1 _ orig (RBI.origrb r) _ (popStackInvariant _ _ _ _ _ (popStackInvariant _ _ _ _ _ rb00))
        rb09 : RBtreeInvariant (PG.parent pg)
        rb09 = PGtoRBinvariant1 _ orig (RBI.origrb r) _ (popStackInvariant _ _ _ _ _ rb00)
        rb08 : treeInvariant (PG.parent pg)
        rb08 = siToTreeinvariant _ _ _ _ (RBI.origti r) (popStackInvariant _ _ _ _ _ rb00)

        insertCase51 : t
        insertCase51 with PG.pg pg
        ... | s2-s1p2 {kp} {kg} {vp} {vg} {n1} {n2} lt lt2 x x₁ = insertCase52 where
          insertCase52 : t
          insertCase52 = next (PG.grand pg ∷ PG.rest pg) record {
            tree = PG.grand pg
            ; repl = rb01
            ; origti = RBI.origti r
            ; origrb = RBI.origrb r
            ; treerb = rb02
            ; replrb = subst (λ k → RBtreeInvariant k) rb10 (rb-black _ _ rb18 (RBI.replrb r) (rb-red _ _ rb16 uncle-black rb19 rb06 rb05))
            ; replti = RB-repl→ti _ _ _ _  (siToTreeinvariant _ _ _ _ (RBI.origti r) (popStackInvariant _ _ _ _ _ (popStackInvariant _ _ _ _ _ rb00))) rb11
            ; si = popStackInvariant _ _ _ _ _ (popStackInvariant _ _ _ _ _ rb00)
            ; state = rebuild (trans (cong color x₁) (cong proj1 (sym rb14))) rb17 (subst (λ k → ¬ (k ≡ leaf)) (sym x₁) (λ ())) rb11
           } rb15 where
            rb01 : bt (Color ∧ A)
            rb01 = to-black (node kp vp (node rkey vr rp-left rp-right) (to-red (node kg vg n1 (PG.uncle pg))))
            rb04 : key < kp
            rb04 = lt
            rb16 : color n1 ≡ Black
            rb16 = proj2 (RBtreeChildrenColorBlack _ _ (subst (λ k → RBtreeInvariant k) x rb09) (trans (cong color (sym x)) pcolor))
            rb13 : ⟪ Red , proj2 vp ⟫ ≡ vp
            rb13 with subst (λ k → color k ≡ Red ) x pcolor
            ... | refl = refl
            rb14 : ⟪ Black , proj2 vg ⟫ ≡ vg
            rb14 with RBtreeParentColorBlack _ _ (subst (λ k → RBtreeInvariant k) x₁ rb02) (case1 pcolor)
            ... | refl = refl
            rb03 : replacedRBTree key value (node kg _ (node kp ⟪ Red , proj2 vp ⟫ (RBI.tree r) n1) (PG.uncle pg))
                (node kp ⟪ Black , proj2 vp ⟫  repl (node kg ⟪ Red , proj2 vg ⟫ n1 (PG.uncle pg)))
            rb03 = rbr-rotate-ll repl-red rb04 rot
            rb10 : node kp ⟪ Black , proj2 vp ⟫ repl (node kg ⟪ Red , proj2 vg ⟫ n1 (PG.uncle pg)) ≡ rb01
            rb10 = begin
               to-black (node kp vp repl (to-red (node kg vg n1 (PG.uncle pg)))) ≡⟨ cong (λ k → node _ _ k _) (sym eq) ⟩
               rb01 ∎ where open ≡-Reasoning
            rb12 : node kg ⟪ Black , proj2 vg ⟫ (node kp ⟪ Red , proj2 vp ⟫ (RBI.tree r) n1) (PG.uncle pg) ≡ PG.grand pg
            rb12 = begin
                 node kg ⟪ Black , proj2 vg ⟫ (node kp ⟪ Red , proj2 vp ⟫ (RBI.tree r) n1) (PG.uncle pg)
                    ≡⟨ cong₂ (λ j k → node kg j (node kp k (RBI.tree r) n1) (PG.uncle pg) ) rb14 rb13 ⟩
                 node kg vg _ (PG.uncle pg) ≡⟨ cong (λ k → node _ _ k _) (sym x) ⟩
                 node kg vg (PG.parent pg) (PG.uncle pg) ≡⟨ sym x₁ ⟩
                 PG.grand pg ∎ where open ≡-Reasoning
            rb11 : replacedRBTree key value (PG.grand pg) rb01
            rb11 = subst₂ (λ j k → replacedRBTree key value j k) rb12 rb10 rb03
            rb05 : RBtreeInvariant (PG.uncle pg)
            rb05 = RBtreeRightDown _ _ (subst (λ k → RBtreeInvariant k) x₁ rb02)
            rb06 : RBtreeInvariant n1
            rb06 = RBtreeRightDown _ _ (subst (λ k → RBtreeInvariant k) x rb09)
            rb19 : black-depth n1 ≡ black-depth (PG.uncle pg)
            rb19 = trans (sym ( proj2 (red-children-eq x (sym (cong proj1 rb13))  rb09) )) (RBtreeEQ (subst (λ k → RBtreeInvariant k) x₁ rb02))
            rb18 : black-depth repl ≡ black-depth n1 ⊔ black-depth (PG.uncle pg)
            rb18 = begin
               black-depth repl ≡⟨ sym (RB-repl→eq _ _ (RBI.treerb r) rot) ⟩
               black-depth (RBI.tree r) ≡⟨ RBtreeEQ (subst (λ k → RBtreeInvariant k) x rb09) ⟩
               black-depth n1 ≡⟨ sym (⊔-idem (black-depth n1)) ⟩
               black-depth n1 ⊔ black-depth n1 ≡⟨ cong (λ k → black-depth n1 ⊔ k) rb19 ⟩
               black-depth n1 ⊔ black-depth (PG.uncle pg) ∎ where open ≡-Reasoning
            rb17 : suc (black-depth (node rkey vr rp-left rp-right) ⊔ (black-depth n1 ⊔ black-depth (PG.uncle pg))) ≡ black-depth (PG.grand pg)
            rb17 = begin
                suc (black-depth (node rkey vr rp-left rp-right) ⊔ (black-depth n1 ⊔ black-depth (PG.uncle pg)))
                     ≡⟨ cong₂ (λ j k → suc (black-depth j ⊔ k)) eq (sym rb18) ⟩
                suc (black-depth repl ⊔ black-depth repl) ≡⟨ ⊔-idem _ ⟩
                suc (black-depth repl ) ≡⟨ cong suc (sym (RB-repl→eq _ _ (RBI.treerb r) rot)) ⟩
                suc (black-depth (RBI.tree r) ) ≡⟨ cong suc (sym (proj1 (red-children-eq x (cong proj1 (sym rb13)) rb09))) ⟩
                suc (black-depth (PG.parent pg) ) ≡⟨ sym (proj1 (black-children-eq refl (cong proj1 (sym rb14)) (subst (λ k → RBtreeInvariant k) x₁ rb02))) ⟩
                black-depth (node kg vg (PG.parent pg) (PG.uncle pg)) ≡⟨ cong black-depth (sym x₁) ⟩
                black-depth (PG.grand pg) ∎ where open ≡-Reasoning
                -- outer case, repl  is not decomposed
                -- lt          : key < kp
                -- x           : PG.parent pg ≡ node kp vp (RBI.tree r) n1
                -- x₁          : PG.grand pg ≡ node kg vg (PG.parent pg) (PG.uncle pg)
                -- eq          : node rkey vr rp-left rp-right ≡ RBI.repl r
        ... | s2-1sp2 {kp} {kg} {vp} {vg} {n1} {n2} lt lt2 x x₁ = insertCase52 where
          insertCase52 : t
          insertCase52 = next (PG.grand pg ∷ PG.rest pg) record {
            tree = PG.grand pg
            ; repl = rb01
            ; origti = RBI.origti r
            ; origrb = RBI.origrb r
            ; treerb = rb02
            ; replrb = rb10
            ; replti =  RB-repl→ti _ _ _ _  (siToTreeinvariant _ _ _ _ (RBI.origti r) (popStackInvariant _ _ _ _ _ (popStackInvariant _ _ _ _ _ rb00))) rb11
            ; si = popStackInvariant _ _ _ _ _ (popStackInvariant _ _ _ _ _ rb00)
            ; state = rebuild rb33 rb17 (subst (λ k → ¬ (k ≡ leaf)) (sym x₁) (λ ())) rb11
           } rb15 where
                -- inner case, repl  is decomposed
                -- lt          : kp < key
                -- x           : PG.parent pg ≡ node kp vp n1 (RBI.tree r)
                -- x₁          : PG.grand pg ≡ node kg vg (PG.parent pg) (PG.uncle pg)
                -- eq          : node rkey vr rp-left rp-right ≡ RBI.repl r
            rb01 : bt (Color ∧ A)
            rb01 = to-black (node rkey vr (node kp vp n1 rp-left) (to-red (node kg vg rp-right (PG.uncle pg))))
            rb04 : kp < key
            rb04 = lt
            rb21 : key < kg   -- this can be a part of ParentGand relation
            rb21 = lt2 -- si-property-< (subst (λ k → ¬ (k ≡ leaf)) (sym x) (λ ())) (subst (λ k → treeInvariant k ) x₁ (siToTreeinvariant _ _ _ _ (RBI.origti r)
                 -- (popStackInvariant _ _ _ _ _ (popStackInvariant _ _ _ _ _ rb00))))
                 -- (subst (λ k → stackInvariant key _ orig (PG.parent pg ∷ k ∷ PG.rest pg)) x₁ (popStackInvariant _ _ _ _ _ rb00))
            rb16 : color n1 ≡ Black
            rb16 = proj1 (RBtreeChildrenColorBlack _ _ (subst (λ k → RBtreeInvariant k) x rb09) (trans (cong color (sym x)) pcolor))
            rb13 : ⟪ Red , proj2 vp ⟫ ≡ vp
            rb13 with subst (λ k → color k ≡ Red ) x pcolor
            ... | refl = refl
            rb14 : ⟪ Black , proj2 vg ⟫ ≡ vg
            rb14 with RBtreeParentColorBlack _ _ (subst (λ k → RBtreeInvariant k) x₁ rb02) (case1 pcolor)
            ... | refl = refl
            rb33 : color (PG.grand pg) ≡ Black
            rb33 = subst (λ k → color k ≡ Black ) (sym x₁) (sym (cong proj1 rb14))
            rb23 :  vr ≡ ⟪ Red , proj2 vr ⟫
            rb23 with subst (λ k → color k ≡ Red ) (sym eq) repl-red
            ... | refl = refl
            rb20 : color rp-right ≡ Black
            rb20 = proj2 (RBtreeChildrenColorBlack _ _ (subst (λ k → RBtreeInvariant k) (sym eq) (RBI.replrb r) ) (cong proj1 rb23))
            rb03 : replacedRBTree key value (node kg _ (node kp _ n1 (RBI.tree r)) (PG.uncle pg))
               (node rkey ⟪ Black , proj2 vr ⟫ (node kp ⟪ Red , proj2 vp ⟫  n1 rp-left) (node kg ⟪ Red , proj2 vg ⟫ rp-right (PG.uncle pg)))
            rb03 = rbr-rotate-lr rp-left rp-right kg kp rkey rb20 rb04 rb21
                (subst (λ k → replacedRBTree key value (RBI.tree r) k) (trans (sym eq) (cong (λ k → node rkey k rp-left rp-right) rb23 )) rot )
            rb24 : node kg ⟪ Black , proj2 vg ⟫ (node kp ⟪ Red , proj2 vp ⟫ n1 (RBI.tree r)) (PG.uncle pg) ≡ PG.grand pg
            rb24 = trans (trans (cong₂ (λ j k → node kg j (node kp k n1 (RBI.tree r)) (PG.uncle pg)) rb14 rb13 ) (cong (λ k → node kg vg k (PG.uncle pg)) (sym x))) (sym x₁)
            rb25 : node rkey ⟪ Black , proj2 vr ⟫ (node kp ⟪ Red , proj2 vp ⟫ n1 rp-left) (node kg ⟪ Red , proj2 vg ⟫ rp-right (PG.uncle pg)) ≡ rb01
            rb25 = begin
                node rkey ⟪ Black , proj2 vr ⟫ (node kp ⟪ Red , proj2 vp ⟫ n1 rp-left) (node kg ⟪ Red , proj2 vg ⟫ rp-right (PG.uncle pg))
                     ≡⟨ cong (λ k → node _ _ (node kp k  n1 rp-left) _ ) rb13 ⟩
                node rkey ⟪ Black , proj2 vr ⟫ (node kp vp n1 rp-left) (node kg ⟪ Red , proj2 vg ⟫ rp-right (PG.uncle pg))  ≡⟨ refl  ⟩
                rb01 ∎ where open ≡-Reasoning
            rb11 : replacedRBTree key value (PG.grand pg) rb01
            rb11 = subst₂ (λ j k → replacedRBTree key value j k) rb24 rb25 rb03
            rb05 : RBtreeInvariant (PG.uncle pg)
            rb05 = RBtreeRightDown _ _ (subst (λ k → RBtreeInvariant k) x₁ rb02)
            rb06 : RBtreeInvariant n1
            rb06 = RBtreeLeftDown _ _ (subst (λ k → RBtreeInvariant k) x rb09)
            rb26 : RBtreeInvariant rp-left
            rb26 = RBtreeLeftDown _ _ (subst (λ k → RBtreeInvariant k) (sym eq) (RBI.replrb r))
            rb28 : RBtreeInvariant rp-right
            rb28 = RBtreeRightDown _ _ (subst (λ k → RBtreeInvariant k) (sym eq) (RBI.replrb r))
            rb31 : RBtreeInvariant (node rkey vr rp-left rp-right )
            rb31 = subst (λ k → RBtreeInvariant k) (sym eq) (RBI.replrb r)
            rb18 : black-depth rp-right ≡ black-depth (PG.uncle pg)
            rb18 = begin
                black-depth rp-right ≡⟨ sym ( proj2 (red-children-eq1 (sym eq) repl-red (RBI.replrb r) )) ⟩
                black-depth (RBI.repl r) ≡⟨ sym (RB-repl→eq _ _ (RBI.treerb r) rot) ⟩
                black-depth (RBI.tree r) ≡⟨ sym (proj2 (red-children-eq1 x pcolor rb09) ) ⟩
                black-depth (PG.parent pg) ≡⟨ RBtreeEQ (subst (λ k → RBtreeInvariant k) x₁ rb02 ) ⟩
                black-depth (PG.uncle pg) ∎ where open ≡-Reasoning
            rb27 : black-depth n1 ≡ black-depth rp-left
            rb27 = begin
               black-depth n1 ≡⟨ RBtreeEQ (subst (λ k → RBtreeInvariant k) x rb09) ⟩
               black-depth (RBI.tree r) ≡⟨ RB-repl→eq _ _ (RBI.treerb r) rot ⟩
               black-depth (RBI.repl r) ≡⟨ proj1 (red-children-eq1 (sym eq) repl-red (RBI.replrb r)) ⟩
               black-depth rp-left ∎
                  where open ≡-Reasoning
            rb19 : black-depth (node kp vp n1 rp-left) ≡ black-depth rp-right ⊔ black-depth (PG.uncle pg)
            rb19 = begin
                black-depth (node kp vp n1 rp-left) ≡⟨ black-depth-resp A (node kp vp n1 rp-left) (node kp vp rp-left rp-left)  refl refl refl rb27 refl ⟩
                black-depth (node kp vp rp-left rp-left) ≡⟨ black-depth-resp A (node kp vp rp-left rp-left) (node rkey vr rp-left rp-right)
                     refl refl (trans (sym (cong proj1 rb13)) (sym (cong proj1 rb23))) refl (RBtreeEQ (subst (λ k → RBtreeInvariant k) (sym eq) (RBI.replrb r))) ⟩
                black-depth (node rkey vr rp-left rp-right) ≡⟨ black-depth-cong A eq ⟩
                black-depth (RBI.repl r) ≡⟨ proj2 (red-children-eq1 (sym eq) repl-red (RBI.replrb r)) ⟩
                black-depth rp-right ≡⟨ sym ( ⊔-idem _ ) ⟩
                black-depth rp-right ⊔ black-depth rp-right ≡⟨ cong (λ k → black-depth rp-right ⊔ k) rb18 ⟩
                black-depth rp-right ⊔ black-depth (PG.uncle pg) ∎
                  where open ≡-Reasoning
            rb29 : color n1 ≡ Black
            rb29 = proj1 (RBtreeChildrenColorBlack _ _ (subst (λ k → RBtreeInvariant k) x rb09) (sym (cong proj1 rb13)) )
            rb30 : color rp-left ≡ Black
            rb30 = proj1 (RBtreeChildrenColorBlack _ _ (subst (λ k → RBtreeInvariant k) (sym eq) (RBI.replrb r)) (cong proj1 rb23))
            rb32 : suc (black-depth (PG.uncle pg)) ≡ black-depth (PG.grand pg)
            rb32 = sym (proj2 ( black-children-eq1 x₁ rb33 rb02 ))
            rb10 : RBtreeInvariant (node rkey ⟪ Black , proj2 vr ⟫ (node kp vp n1 rp-left) (node kg ⟪ Red , proj2 vg ⟫ rp-right (PG.uncle pg)))
            rb10 = rb-black _ _ rb19 (rbi-from-red-black _ _ kp vp rb06 rb26 rb27 rb29 rb30 rb13) (rb-red _ _ rb20 uncle-black rb18 rb28 rb05)
            rb17 : suc (black-depth (node kp vp n1 rp-left) ⊔ (black-depth rp-right ⊔ black-depth (PG.uncle pg))) ≡ black-depth (PG.grand pg)
            rb17 = begin
                 suc (black-depth (node kp vp n1 rp-left) ⊔ (black-depth rp-right ⊔ black-depth (PG.uncle pg))) ≡⟨ cong (λ k → suc (k ⊔ _)) rb19 ⟩
                 suc ((black-depth rp-right ⊔ black-depth (PG.uncle pg)) ⊔ (black-depth rp-right ⊔ black-depth (PG.uncle pg))) ≡⟨ cong suc ( ⊔-idem _) ⟩
                 suc (black-depth rp-right ⊔ black-depth (PG.uncle pg))  ≡⟨ cong (λ k → suc (k ⊔ _)) rb18 ⟩
                 suc (black-depth (PG.uncle pg) ⊔ black-depth (PG.uncle pg)) ≡⟨ cong suc (⊔-idem _) ⟩
                 suc (black-depth (PG.uncle pg))  ≡⟨ rb32 ⟩
                 black-depth (PG.grand pg) ∎
                 where open ≡-Reasoning
        ... | s2-s12p {kp} {kg} {vp} {vg} {n1} {n2} lt lt2 x x₁ = insertCase52 where
          insertCase52 : t
          insertCase52 = next (PG.grand pg ∷ PG.rest pg) record {
            tree = PG.grand pg
            ; repl = rb01
            ; origti = RBI.origti r
            ; origrb = RBI.origrb r
            ; treerb = rb02
            ; replrb = rb10
            ; replti = RB-repl→ti _ _ _ _  (siToTreeinvariant _ _ _ _ (RBI.origti r) (popStackInvariant _ _ _ _ _ (popStackInvariant _ _ _ _ _ rb00))) rb11
            ; si = popStackInvariant _ _ _ _ _ (popStackInvariant _ _ _ _ _ rb00)
            ; state = rebuild rb33 rb17 (subst (λ k → ¬ (k ≡ leaf)) (sym x₁) (λ ())) rb11
           } rb15 where
                -- inner case, repl  is decomposed
                -- lt          : key < kp
                -- x           : PG.parent pg ≡ node kp vp (RBI.tree r) n1
                -- x₁          : PG.grand pg ≡ node kg vg (PG.uncle pg) (PG.parent pg)
                -- eq          : node rkey vr rp-left rp-right ≡ RBI.repl r
            rb01 : bt (Color ∧ A)
            rb01 = to-black (node rkey vr (to-red (node kg vg (PG.uncle pg) rp-left )) (node kp vp rp-right n1))
            rb04 : key < kp
            rb04 = lt
            rb21 : kg < key   -- this can be a part of ParentGand relation
            rb21 = lt2 -- si-property-> (subst (λ k → ¬ (k ≡ leaf)) (sym x) (λ ())) (subst (λ k → treeInvariant k ) x₁ (siToTreeinvariant _ _ _ _ (RBI.origti r)
                 -- (popStackInvariant _ _ _ _ _ (popStackInvariant _ _ _ _ _ rb00))))
                 -- (subst (λ k → stackInvariant key _ orig (PG.parent pg ∷ k ∷ PG.rest pg)) x₁ (popStackInvariant _ _ _ _ _ rb00))
            rb16 : color n1 ≡ Black
            rb16 = proj2 (RBtreeChildrenColorBlack _ _ (subst (λ k → RBtreeInvariant k) x rb09) (trans (cong color (sym x)) pcolor))
            rb13 : ⟪ Red , proj2 vp ⟫ ≡ vp
            rb13 with subst (λ k → color k ≡ Red ) x pcolor
            ... | refl = refl
            rb14 : ⟪ Black , proj2 vg ⟫ ≡ vg
            rb14 with RBtreeParentColorBlack _ _ (subst (λ k → RBtreeInvariant k) x₁ rb02) (case2 pcolor)
            ... | refl = refl
            rb33 : color (PG.grand pg) ≡ Black
            rb33 = subst (λ k → color k ≡ Black ) (sym x₁) (sym (cong proj1 rb14))
            rb23 :  vr ≡ ⟪ Red , proj2 vr ⟫
            rb23 with subst (λ k → color k ≡ Red ) (sym eq) repl-red
            ... | refl = refl
            rb20 : color rp-right ≡ Black
            rb20 = proj2 (RBtreeChildrenColorBlack _ _ (subst (λ k → RBtreeInvariant k) (sym eq) (RBI.replrb r) ) (cong proj1 rb23))
            rb03 : replacedRBTree key value (node kg _ (PG.uncle pg) (node kp _ (RBI.tree r) n1 ))
               (node rkey ⟪ Black , proj2 vr ⟫ (node kg ⟪ Red , proj2 vg ⟫ (PG.uncle pg) rp-left ) (node kp ⟪ Red , proj2 vp ⟫  rp-right n1 ))
            rb03 = rbr-rotate-rl rp-left rp-right kg kp rkey rb20 rb21 rb04
                (subst (λ k → replacedRBTree key value (RBI.tree r) k) (trans (sym eq) (cong (λ k → node rkey k rp-left rp-right) rb23 )) rot )
            rb24 : node kg ⟪ Black , proj2 vg ⟫ (PG.uncle pg) (node kp ⟪ Red , proj2 vp ⟫ (RBI.tree r) n1) ≡ PG.grand pg
            rb24 = begin
               node kg ⟪ Black , proj2 vg ⟫ (PG.uncle pg) (node kp ⟪ Red , proj2 vp ⟫ (RBI.tree r) n1)
                   ≡⟨ cong₂ (λ j k → node kg j (PG.uncle pg) (node kp k (RBI.tree r) n1) ) rb14 rb13 ⟩
               node kg vg (PG.uncle pg) (node kp vp (RBI.tree r) n1) ≡⟨ cong (λ k → node kg vg (PG.uncle pg) k ) (sym x) ⟩
               node kg vg (PG.uncle pg) (PG.parent pg) ≡⟨ sym x₁ ⟩
               PG.grand pg ∎ where open ≡-Reasoning
            rb25 : node rkey ⟪ Black , proj2 vr ⟫ (node kg ⟪ Red , proj2 vg ⟫ (PG.uncle pg) rp-left) (node kp ⟪ Red , proj2 vp ⟫ rp-right n1) ≡ rb01
            rb25 = begin
                node rkey ⟪ Black , proj2 vr ⟫ (node kg ⟪ Red , proj2 vg ⟫ (PG.uncle pg) rp-left) (node kp ⟪ Red , proj2 vp ⟫ rp-right n1)
                        ≡⟨ cong (λ k → node rkey ⟪ Black , proj2 vr ⟫ (node kg ⟪ Red , proj2 vg ⟫ (PG.uncle pg) rp-left) (node kp k rp-right n1)) rb13  ⟩
                node rkey ⟪ Black , proj2 vr ⟫ (node kg ⟪ Red , proj2 vg ⟫ (PG.uncle pg) rp-left) (node kp vp rp-right n1)  ≡⟨ refl ⟩
                rb01 ∎ where open ≡-Reasoning
            rb11 : replacedRBTree key value (PG.grand pg) rb01
            rb11 = subst₂ (λ j k → replacedRBTree key value j k) rb24 rb25 rb03
            rb05 : RBtreeInvariant (PG.uncle pg)
            rb05 = RBtreeLeftDown _ _ (subst (λ k → RBtreeInvariant k) x₁ rb02)
            rb06 : RBtreeInvariant n1
            rb06 = RBtreeRightDown _ _ (subst (λ k → RBtreeInvariant k) x rb09)
            rb26 : RBtreeInvariant rp-left
            rb26 = RBtreeLeftDown _ _ (subst (λ k → RBtreeInvariant k) (sym eq) (RBI.replrb r))
            rb28 : RBtreeInvariant rp-right
            rb28 = RBtreeRightDown _ _ (subst (λ k → RBtreeInvariant k) (sym eq) (RBI.replrb r))
            rb31 : RBtreeInvariant (node rkey vr rp-left rp-right )
            rb31 = subst (λ k → RBtreeInvariant k) (sym eq) (RBI.replrb r)
            rb18 : black-depth (PG.uncle pg) ≡ black-depth rp-left
            rb18 = sym ( begin
                black-depth rp-left ≡⟨ sym ( proj1 (red-children-eq1 (sym eq) repl-red (RBI.replrb r) )) ⟩
                black-depth (RBI.repl r) ≡⟨ sym (RB-repl→eq _ _ (RBI.treerb r) rot) ⟩
                black-depth (RBI.tree r) ≡⟨ sym (proj1 (red-children-eq1 x pcolor rb09) ) ⟩
                black-depth (PG.parent pg) ≡⟨ sym (RBtreeEQ (subst (λ k → RBtreeInvariant k) x₁ rb02 )) ⟩
                black-depth (PG.uncle pg) ∎ ) where open ≡-Reasoning
            rb27 : black-depth rp-right ≡ black-depth n1
            rb27 = sym ( begin
               black-depth n1 ≡⟨ sym (RBtreeEQ (subst (λ k → RBtreeInvariant k) x rb09)) ⟩
               black-depth (RBI.tree r) ≡⟨ RB-repl→eq _ _ (RBI.treerb r) rot ⟩
               black-depth (RBI.repl r) ≡⟨ proj2 (red-children-eq1 (sym eq) repl-red (RBI.replrb r)) ⟩
               black-depth rp-right ∎ )
                  where open ≡-Reasoning
            rb19 : black-depth (PG.uncle pg) ⊔ black-depth rp-left ≡ black-depth (node kp vp rp-right n1)
            rb19 = sym ( begin
                black-depth (node kp vp rp-right n1)  ≡⟨ black-depth-resp A (node kp vp rp-right n1) (node kp vp rp-right rp-right)  refl refl refl refl (sym rb27) ⟩
                black-depth (node kp vp rp-right rp-right) ≡⟨ black-depth-resp A (node kp vp rp-right rp-right) (node rkey vr rp-left rp-right)
                     refl refl (trans (sym (cong proj1 rb13)) (sym (cong proj1 rb23))) (sym (RBtreeEQ (subst (λ k → RBtreeInvariant k) (sym eq) (RBI.replrb r)))) refl ⟩
                black-depth (node rkey vr rp-left rp-right) ≡⟨ black-depth-cong A eq ⟩
                black-depth (RBI.repl r) ≡⟨ proj1 (red-children-eq1 (sym eq) repl-red (RBI.replrb r)) ⟩
                black-depth rp-left ≡⟨ sym ( ⊔-idem _ ) ⟩
                black-depth  rp-left ⊔ black-depth rp-left ≡⟨ cong (λ k → k ⊔ black-depth rp-left ) (sym rb18) ⟩
                black-depth (PG.uncle pg) ⊔ black-depth rp-left ∎ )
                  where open ≡-Reasoning
            rb29 : color n1 ≡ Black
            rb29 = proj2 (RBtreeChildrenColorBlack _ _ (subst (λ k → RBtreeInvariant k) x rb09) (sym (cong proj1 rb13)) )
            rb30 : color rp-left ≡ Black
            rb30 = proj1 (RBtreeChildrenColorBlack _ _ (subst (λ k → RBtreeInvariant k) (sym eq) (RBI.replrb r)) (cong proj1 rb23))
            rb32 : suc (black-depth (PG.uncle pg)) ≡ black-depth (PG.grand pg)
            rb32 = sym (proj1 ( black-children-eq1 x₁ rb33 rb02 ))
            rb10 : RBtreeInvariant (node rkey ⟪ Black , proj2 vr ⟫ (node kg ⟪ Red , proj2 vg ⟫ (PG.uncle pg) rp-left ) (node kp vp rp-right n1) )
            rb10 = rb-black _ _ rb19 (rb-red _ _ uncle-black rb30 rb18 rb05 rb26 ) (rbi-from-red-black _ _ _ _ rb28 rb06 rb27 rb20 rb16 rb13 )
            rb17 : suc (black-depth (PG.uncle pg) ⊔ black-depth rp-left ⊔ black-depth (node kp vp rp-right n1)) ≡ black-depth (PG.grand pg)
            rb17 = begin
                 suc (black-depth (PG.uncle pg) ⊔ black-depth rp-left ⊔ black-depth (node kp vp rp-right n1)) ≡⟨ cong (λ k → suc (_ ⊔ k)) (sym rb19) ⟩
                 suc (black-depth (PG.uncle pg) ⊔ black-depth rp-left ⊔ (black-depth (PG.uncle pg) ⊔ black-depth rp-left)) ≡⟨ cong suc ( ⊔-idem _) ⟩
                 suc (black-depth (PG.uncle pg) ⊔ black-depth rp-left ) ≡⟨ cong (λ k → suc (_ ⊔ k)) (sym rb18) ⟩
                 suc (black-depth (PG.uncle pg) ⊔ black-depth (PG.uncle pg)) ≡⟨ cong suc (⊔-idem _) ⟩
                 suc (black-depth (PG.uncle pg))  ≡⟨ rb32 ⟩
                 black-depth (PG.grand pg) ∎
                    where open ≡-Reasoning
        ... | s2-1s2p {kp} {kg} {vp} {vg} {n1} {n2} lt lt2 x x₁ = insertCase52 where
          insertCase52 : t
          insertCase52 = next (PG.grand pg ∷ PG.rest pg) record {
            tree = PG.grand pg
            ; repl = rb01
            ; origti = RBI.origti r
            ; origrb = RBI.origrb r
            ; treerb = rb02
            ; replrb = subst (λ k → RBtreeInvariant k) rb10 (rb-black _ _ rb18 (rb-red _ _ uncle-black rb16 rb19 rb05 rb06) (RBI.replrb r) )
            ; replti = RB-repl→ti _ _ _ _  (siToTreeinvariant _ _ _ _ (RBI.origti r) (popStackInvariant _ _ _ _ _ (popStackInvariant _ _ _ _ _ rb00))) rb11
            ; si = popStackInvariant _ _ _ _ _ (popStackInvariant _ _ _ _ _ rb00)
            ; state = rebuild rb33 rb17 (subst (λ k → ¬ (k ≡ leaf)) (sym x₁) (λ ())) rb11
           } rb15 where
                -- outer case, repl  is not decomposed
                -- lt          : kp < key
                -- x           : PG.parent pg ≡ node kp vp n1 (RBI.tree r)
                -- x₁          : PG.grand pg ≡ node kg vg (PG.uncle pg) (PG.parent pg)
            rb01 : bt (Color ∧ A)
            rb01 = to-black (node kp vp  (to-red (node kg vg (PG.uncle pg) n1) )(node rkey vr rp-left rp-right))
            rb04 : kp < key
            rb04 = lt
            rb16 : color n1 ≡ Black
            rb16 = proj1 (RBtreeChildrenColorBlack _ _ (subst (λ k → RBtreeInvariant k) x rb09) (trans (cong color (sym x)) pcolor))
            rb13 : ⟪ Red , proj2 vp ⟫ ≡ vp
            rb13 with subst (λ k → color k ≡ Red ) x pcolor
            ... | refl = refl
            rb14 : ⟪ Black , proj2 vg ⟫ ≡ vg
            rb14 with RBtreeParentColorBlack _ _ (subst (λ k → RBtreeInvariant k) x₁ rb02) (case2 pcolor)
            ... | refl = refl
            rb33 : color (PG.grand pg) ≡ Black
            rb33 = subst (λ k → color k ≡ Black ) (sym x₁) (sym (cong proj1 rb14))
            rb03 : replacedRBTree key value (node kg _ (PG.uncle pg) (node kp ⟪ Red , proj2 vp ⟫ n1 (RBI.tree r) ))
                (node kp ⟪ Black , proj2 vp ⟫  (node kg ⟪ Red , proj2 vg ⟫ (PG.uncle pg) n1 ) repl )
            rb03 = rbr-rotate-rr repl-red rb04 rot
            rb10 : node kp ⟪ Black , proj2 vp ⟫ (node kg ⟪ Red , proj2 vg ⟫ (PG.uncle pg) n1 ) repl ≡ rb01
            rb10 = cong (λ  k → node _ _  _ k ) (sym eq)
            rb12 : node kg ⟪ Black , proj2 vg ⟫ (PG.uncle pg) (node kp ⟪ Red , proj2 vp ⟫ n1 (RBI.tree r)) ≡ PG.grand pg
            rb12 = begin
                 node kg ⟪ Black , proj2 vg ⟫ (PG.uncle pg) (node kp ⟪ Red , proj2 vp ⟫ n1 (RBI.tree r))
                       ≡⟨ cong₂ (λ j k → node kg j (PG.uncle pg) (node kp k n1 (RBI.tree r) ) ) rb14 rb13 ⟩
                 node kg vg (PG.uncle pg) _ ≡⟨ cong (λ k → node _ _ _ k) (sym x) ⟩
                 node kg vg (PG.uncle pg) (PG.parent pg) ≡⟨ sym x₁ ⟩
                 PG.grand pg ∎ where open ≡-Reasoning
            rb11 : replacedRBTree key value (PG.grand pg) rb01
            rb11 = subst₂ (λ j k → replacedRBTree key value j k) rb12 rb10 rb03
            rb05 : RBtreeInvariant (PG.uncle pg)
            rb05 = RBtreeLeftDown _ _ (subst (λ k → RBtreeInvariant k) x₁ rb02)
            rb06 : RBtreeInvariant n1
            rb06 = RBtreeLeftDown _ _ (subst (λ k → RBtreeInvariant k) x rb09)
            rb19 : black-depth (PG.uncle pg) ≡ black-depth n1
            rb19 = sym (trans (sym ( proj1 (red-children-eq x (sym (cong proj1 rb13))  rb09) )) (sym (RBtreeEQ (subst (λ k → RBtreeInvariant k) x₁ rb02))))
            rb18 : black-depth (PG.uncle pg) ⊔ black-depth n1 ≡ black-depth repl
            rb18 = sym ( begin
               black-depth repl ≡⟨ sym (RB-repl→eq _ _ (RBI.treerb r) rot) ⟩
               black-depth (RBI.tree r) ≡⟨ sym ( RBtreeEQ (subst (λ k → RBtreeInvariant k) x rb09)) ⟩
               black-depth n1 ≡⟨ sym (⊔-idem (black-depth n1)) ⟩
               black-depth n1 ⊔ black-depth n1 ≡⟨ cong (λ k → k ⊔ _) (sym rb19) ⟩
               black-depth (PG.uncle pg) ⊔ black-depth n1 ∎ ) where open ≡-Reasoning
            rb17 : suc (black-depth (PG.uncle pg) ⊔ black-depth n1 ⊔ black-depth (node rkey vr rp-left rp-right)) ≡ black-depth (PG.grand pg)
            rb17 = begin
                suc (black-depth (PG.uncle pg) ⊔ black-depth n1 ⊔ black-depth (node rkey vr rp-left rp-right))
                      ≡⟨ cong₂ (λ j k → suc (j ⊔ black-depth k)) rb18 eq  ⟩
                suc (black-depth repl ⊔ black-depth repl) ≡⟨ ⊔-idem _ ⟩
                suc (black-depth repl ) ≡⟨ cong suc (sym (RB-repl→eq _ _ (RBI.treerb r) rot)) ⟩
                suc (black-depth (RBI.tree r) ) ≡⟨ cong suc (sym (proj2 (red-children-eq x (cong proj1 (sym rb13)) rb09))) ⟩
                suc (black-depth (PG.parent pg) ) ≡⟨ sym (proj2 (black-children-eq refl (cong proj1 (sym rb14)) (subst (λ k → RBtreeInvariant k) x₁ rb02))) ⟩
                black-depth (node kg vg (PG.uncle pg) (PG.parent pg)) ≡⟨ cong black-depth (sym x₁) ⟩
                black-depth (PG.grand pg) ∎ where open ≡-Reasoning
    replaceRBP1 : t
    replaceRBP1 with RBI.state r
    ... | rebuild ceq bdepth-eq ¬leaf rot = rebuildCase ceq bdepth-eq ¬leaf rot
    ... | top-black eq rot = exit stack (trans eq (cong (λ k → k ∷ []) rb00)) r where
        rb00 : RBI.tree r ≡ orig
        rb00 = just-injective (si-property-last _ _ _ _ (subst (λ k → stackInvariant key (RBI.tree r) orig k) (eq) (RBI.si r)))
    ... | rotate _ repl-red rot with stackToPG (RBI.tree r) orig stack (RBI.si r)
    ... | case1 eq  = exit stack eq r     -- no stack, replace top node
    ... | case2 (case1 eq) = insertCase4 orig refl eq rot (case1 repl-red) (RBI.si r)     -- one level stack, orig is parent of repl
    ... | case2 (case2 pg) with color (PG.parent pg) in pcolor
    ... | Black = insertCase1 where
       -- Parent is Black, make color repl ≡ color tree then goto rebuildCase
       rb00 : (pg : PG (Color ∧ A) key (RBI.tree r) stack) → stackInvariant key (RBI.tree r) orig (RBI.tree r ∷ PG.parent pg ∷ PG.grand pg ∷ PG.rest pg)
       rb00 pg = subst (λ k → stackInvariant key (RBI.tree r) orig k) (PG.stack=gp pg) (RBI.si r)
       treerb : (pg : PG (Color ∧ A) key (RBI.tree r) stack) → RBtreeInvariant (PG.parent pg)
       treerb pg = PGtoRBinvariant1 _ orig (RBI.origrb r) _ (popStackInvariant _ _ _ _ _ (rb00 pg))
       rb08 : (pg : PG (Color ∧ A) key (RBI.tree r) stack) → treeInvariant (PG.parent pg)
       rb08 pg = siToTreeinvariant _ _ _ _ (RBI.origti r) (popStackInvariant _ _ _ _ _ (rb00 pg))
       insertCase1 : t
       insertCase1 with PG.pg pg
       ... | s2-s1p2 {kp} {kg} {vp} {vg} {n1} {n2} lt lt2 x x₁ = next (PG.parent pg ∷ PG.grand pg ∷ PG.rest pg) record {
            tree = PG.parent pg
            ; repl = rb01
            ; origti = RBI.origti r
            ; origrb = RBI.origrb r
            ; treerb = treerb pg
            ; replrb = rb06
            ; replti = RB-repl→ti _ _ _ _  (siToTreeinvariant _ _ _ _ (RBI.origti r) (popStackInvariant _ _ _ _ _ (rb00 pg))) rb11
            ; si = popStackInvariant _ _ _ _ _ (rb00 pg)
            ; state = rebuild (cong color x)  (rb05 (trans (sym (cong color x)) pcolor)) (subst (λ k → ¬ (k ≡ leaf)) (sym x) (λ ())) rb11
           } (subst₂ (λ j k → j < length k ) refl (sym (PG.stack=gp pg)) ≤-refl) where
            rb01 : bt (Color ∧ A)
            rb01 = node kp vp repl n1
            rb03 : key < kp
            rb03 = lt
            rb04 :  ⟪ Black , proj2 vp ⟫ ≡ vp
            rb04 with subst (λ k → color k ≡ Black) x pcolor
            ... | refl = refl
            rb02 : ⟪ Black , proj2 vp ⟫ ≡ vp → replacedRBTree key value (node kp vp (RBI.tree r) n1) (node kp vp repl n1)
            rb02 eq = subst (λ k → replacedRBTree key value (node kp k (RBI.tree r) n1) (node kp k repl n1)) eq (rbr-black-left repl-red rb03 rot )
            rb07 : black-depth repl ≡ black-depth n1
            rb07 = begin
               black-depth repl ≡⟨ sym (RB-repl→eq _ _ (RBI.treerb r) rot) ⟩
               black-depth (RBI.tree r) ≡⟨ RBtreeEQ (subst (λ k → RBtreeInvariant k) x (treerb pg)) ⟩
               black-depth n1 ∎
                 where open ≡-Reasoning
            rb05 : proj1 vp ≡ Black → black-depth rb01 ≡ black-depth (PG.parent pg)
            rb05 refl = begin
               suc (black-depth repl ⊔ black-depth n1) ≡⟨ cong suc (cong (λ k → k ⊔ black-depth n1) (sym (RB-repl→eq _ _ (RBI.treerb r) rot))) ⟩
               suc (black-depth (RBI.tree r) ⊔ black-depth n1) ≡⟨ refl ⟩
               black-depth (node kp vp (RBI.tree r) n1) ≡⟨ cong black-depth (sym x) ⟩
               black-depth (PG.parent pg) ∎
                 where open ≡-Reasoning
            rb06 : RBtreeInvariant rb01
            rb06 = subst (λ k → RBtreeInvariant (node kp k repl n1))  rb04
               ( rb-black _ _ rb07 (RBI.replrb r) (RBtreeRightDown _ _ (subst (λ k → RBtreeInvariant k) x (treerb pg))))
            rb11 = subst (λ k → replacedRBTree key value k (node kp vp repl n1) ) (sym x) (rb02 rb04 )
       ... | s2-1sp2 {kp} {kg} {vp} {vg} {n1} {n2} lt lt2 x x₁ = next (PG.parent pg ∷ PG.grand pg ∷ PG.rest pg) record {
            tree = PG.parent pg
            ; repl = rb01
            ; origti = RBI.origti r
            ; origrb = RBI.origrb r
            ; treerb = treerb pg
            ; replrb = rb06
            ; replti = RB-repl→ti _ _ _ _  (siToTreeinvariant _ _ _ _ (RBI.origti r) (popStackInvariant _ _ _ _ _ (rb00 pg))) rb11
            ; si = popStackInvariant _ _ _ _ _ (rb00 pg)
            ; state = rebuild (cong color x)  (rb05 (trans (sym (cong color x)) pcolor)) (subst (λ k → ¬ (k ≡ leaf)) (sym x) (λ ()))
                (subst (λ k → replacedRBTree key value k (node kp vp n1 repl) ) (sym x) (rb02 rb04 ))
           } (subst₂ (λ j k → j < length k ) refl (sym (PG.stack=gp pg)) ≤-refl) where
               --- x  : PG.parent pg ≡ node kp vp n1 (RBI.tree r)
               --- x₁ : PG.grand pg ≡ node kg vg (PG.parent pg) (PG.uncle pg)
            rb01 : bt (Color ∧ A)
            rb01 = node kp vp n1 repl
            rb03 : kp < key
            rb03 = lt
            rb04 :  ⟪ Black , proj2 vp ⟫ ≡ vp
            rb04 with subst (λ k → color k ≡ Black) x pcolor
            ... | refl = refl
            rb02 : ⟪ Black , proj2 vp ⟫ ≡ vp → replacedRBTree key value (node kp vp n1 (RBI.tree r) ) (node kp vp n1 repl )
            rb02 eq = subst (λ k → replacedRBTree key value (node kp k n1 (RBI.tree r) ) (node kp k n1 repl )) eq (rbr-black-right repl-red rb03 rot )
            rb07 : black-depth repl ≡ black-depth n1
            rb07 = begin
               black-depth repl ≡⟨ sym (RB-repl→eq _ _ (RBI.treerb r) rot) ⟩
               black-depth (RBI.tree r) ≡⟨ sym ( RBtreeEQ (subst (λ k → RBtreeInvariant k) x (treerb pg))) ⟩
               black-depth n1 ∎
                 where open ≡-Reasoning
            rb05 : proj1 vp ≡ Black → black-depth rb01 ≡ black-depth (PG.parent pg)
            rb05 refl = begin
               suc (black-depth n1 ⊔ black-depth repl) ≡⟨ cong suc (cong (λ k → black-depth n1 ⊔ k ) (sym (RB-repl→eq _ _ (RBI.treerb r) rot))) ⟩
               suc (black-depth n1 ⊔ black-depth (RBI.tree r)) ≡⟨ refl ⟩
               black-depth (node kp vp n1 (RBI.tree r) ) ≡⟨ cong black-depth (sym x) ⟩
               black-depth (PG.parent pg) ∎
                 where open ≡-Reasoning
            rb06 : RBtreeInvariant rb01
            rb06 = subst (λ k → RBtreeInvariant (node kp k n1 repl ))  rb04
               ( rb-black _ _ (sym rb07) (RBtreeLeftDown _ _ (subst (λ k → RBtreeInvariant k) x (treerb pg))) (RBI.replrb r) )
            rb11 = subst (λ k → replacedRBTree key value k (node kp vp n1 repl) ) (sym x) (rb02 rb04 )
       insertCase1 | s2-s12p {kp} {kg} {vp} {vg} {n1} {n2} lt lt2 x x₁ = next (PG.parent pg ∷ PG.grand pg ∷ PG.rest pg) record {
            tree = PG.parent pg
            ; repl = rb01
            ; origti = RBI.origti r
            ; origrb = RBI.origrb r
            ; treerb = treerb pg
            ; replrb = rb06
            ; replti = RB-repl→ti _ _ _ _  (siToTreeinvariant _ _ _ _ (RBI.origti r) (popStackInvariant _ _ _ _ _ (rb00 pg))) rb11
            ; si = popStackInvariant _ _ _ _ _ (rb00 pg)
            ; state = rebuild (cong color x)  (rb05 (trans (sym (cong color x)) pcolor)) (subst (λ k → ¬ (k ≡ leaf)) (sym x) (λ ()))
                rb11
           } (subst₂ (λ j k → j < length k ) refl (sym (PG.stack=gp pg)) ≤-refl) where
            rb01 : bt (Color ∧ A)
            rb01 = node kp vp repl n1
            rb03 : key < kp
            rb03 = lt
            rb04 :  ⟪ Black , proj2 vp ⟫ ≡ vp
            rb04 with subst (λ k → color k ≡ Black) x pcolor
            ... | refl = refl
            rb02 : ⟪ Black , proj2 vp ⟫ ≡ vp → replacedRBTree key value (node kp vp (RBI.tree r) n1) (node kp vp repl n1)
            rb02 eq = subst (λ k → replacedRBTree key value (node kp k (RBI.tree r) n1) (node kp k repl n1)) eq (rbr-black-left repl-red rb03 rot )
            rb07 : black-depth repl ≡ black-depth n1
            rb07 = begin
               black-depth repl ≡⟨ sym (RB-repl→eq _ _ (RBI.treerb r) rot) ⟩
               black-depth (RBI.tree r) ≡⟨ RBtreeEQ (subst (λ k → RBtreeInvariant k) x (treerb pg)) ⟩
               black-depth n1 ∎
                 where open ≡-Reasoning
            rb05 : proj1 vp ≡ Black → black-depth rb01 ≡ black-depth (PG.parent pg)
            rb05 refl = begin
               suc (black-depth repl ⊔ black-depth n1) ≡⟨ cong suc (cong (λ k → k ⊔ black-depth n1) (sym (RB-repl→eq _ _ (RBI.treerb r) rot))) ⟩
               suc (black-depth (RBI.tree r) ⊔ black-depth n1) ≡⟨ refl ⟩
               black-depth (node kp vp (RBI.tree r) n1) ≡⟨ cong black-depth (sym x) ⟩
               black-depth (PG.parent pg) ∎
                 where open ≡-Reasoning
            rb06 : RBtreeInvariant rb01
            rb06 = subst (λ k → RBtreeInvariant (node kp k repl n1))  rb04
               ( rb-black _ _ rb07 (RBI.replrb r) (RBtreeRightDown _ _ (subst (λ k → RBtreeInvariant k) x (treerb pg))))
            rb11 = (subst (λ k → replacedRBTree key value k (node kp vp repl n1) ) (sym x) (rb02 rb04 ))
       insertCase1 | s2-1s2p {kp} {kg} {vp} {vg} {n1} {n2} lt lt2 x x₁ = next (PG.parent pg ∷ PG.grand pg ∷ PG.rest pg) record {
            tree = PG.parent pg
            ; repl = rb01
            ; origti = RBI.origti r
            ; origrb = RBI.origrb r
            ; treerb = treerb pg
            ; replrb = rb06
            ; replti = RB-repl→ti _ _ _ _  (siToTreeinvariant _ _ _ _ (RBI.origti r) (popStackInvariant _ _ _ _ _ (rb00 pg))) rb11
            ; si = popStackInvariant _ _ _ _ _ (rb00 pg)
            ; state = rebuild (cong color x)  (rb05 (trans (sym (cong color x)) pcolor)) (subst (λ k → ¬ (k ≡ leaf)) (sym x) (λ ()))
              rb11
           } (subst₂ (λ j k → j < length k ) refl (sym (PG.stack=gp pg)) ≤-refl) where
                -- x   : PG.parent pg ≡ node kp vp (RBI.tree r) n1
                -- x₁  : PG.grand pg ≡ node kg vg (PG.uncle pg) (PG.parent pg)
            rb01 : bt (Color ∧ A)
            rb01 = node kp vp n1 repl
            rb03 : kp < key
            rb03 = lt
            rb04 :  ⟪ Black , proj2 vp ⟫ ≡ vp
            rb04 with subst (λ k → color k ≡ Black) x pcolor
            ... | refl = refl
            rb02 : ⟪ Black , proj2 vp ⟫ ≡ vp → replacedRBTree key value (node kp vp n1 (RBI.tree r) ) (node kp vp n1 repl )
            rb02 eq = subst (λ k → replacedRBTree key value (node kp k n1 (RBI.tree r) ) (node kp k n1 repl )) eq (rbr-black-right repl-red rb03 rot )
            rb07 : black-depth repl ≡ black-depth n1
            rb07 = begin
               black-depth repl ≡⟨ sym (RB-repl→eq _ _ (RBI.treerb r) rot) ⟩
               black-depth (RBI.tree r) ≡⟨ sym ( RBtreeEQ (subst (λ k → RBtreeInvariant k) x (treerb pg))) ⟩
               black-depth n1 ∎
                 where open ≡-Reasoning
            rb05 : proj1 vp ≡ Black → black-depth rb01 ≡ black-depth (PG.parent pg)
            rb05 refl = begin
               suc (black-depth n1 ⊔ black-depth repl) ≡⟨ cong suc (cong (λ k → black-depth n1 ⊔ k ) (sym (RB-repl→eq _ _ (RBI.treerb r) rot))) ⟩
               suc (black-depth n1 ⊔ black-depth (RBI.tree r)) ≡⟨ refl ⟩
               black-depth (node kp vp n1 (RBI.tree r) ) ≡⟨ cong black-depth (sym x) ⟩
               black-depth (PG.parent pg) ∎
                 where open ≡-Reasoning
            rb06 : RBtreeInvariant rb01
            rb06 = subst (λ k → RBtreeInvariant (node kp k n1 repl ))  rb04
               ( rb-black _ _ (sym rb07) (RBtreeLeftDown _ _ (subst (λ k → RBtreeInvariant k) x (treerb pg))) (RBI.replrb r) )
            rb11 =   (subst (λ k → replacedRBTree key value k (node kp vp n1 repl) ) (sym x) (rb02 rb04 ))
    ... | Red with PG.uncle pg in uneq
    ... | leaf = insertCase5 repl refl pg rot repl-red (cong color uneq) pcolor
    ... | node key₁ ⟪ Black , value₁ ⟫ t₁ t₂ = insertCase5 repl refl pg rot repl-red (cong color uneq) pcolor
    ... | node key₁ ⟪ Red , value₁ ⟫ t₁ t₂ with PG.pg pg   -- insertCase2 : uncle and parent are Red, flip color and go up by two level
    ... | s2-s1p2 {kp} {kg} {vp} {vg} {n1} {n2} lt lt2 x x₁ = insertCase2 where
        insertCase2 : t
        insertCase2 = next  (PG.grand pg ∷ (PG.rest pg))
            record {
                 tree = PG.grand pg
                 ; repl = to-red (node kg vg (to-black (node kp vp repl n1)) (to-black (PG.uncle pg)))
                 ; origti = RBI.origti r
                 ; origrb = RBI.origrb r
                 ; treerb = rb01
                 ; replrb = rb-red _ _ refl (RBtreeToBlackColor _ rb02) rb12 (rb-black _ _ rb13 (RBI.replrb r) rb04) (RBtreeToBlack _ rb02)
                 ; replti = RB-repl→ti _ _ _ _  (siToTreeinvariant _ _ _ _ (RBI.origti r) (popStackInvariant _ _ _ _ _ (popStackInvariant _ _ _ _ _ rb00))) rb20
                 ; si = popStackInvariant _ _ _ _ _ (popStackInvariant _ _ _ _ _ rb00)
                 ; state = rotate _ refl rb20
             }  rb15 where
               rb00 : stackInvariant key (RBI.tree r) orig (RBI.tree r ∷ PG.parent pg ∷ PG.grand pg ∷ PG.rest pg)
               rb00 = subst (λ k → stackInvariant key (RBI.tree r) orig k) (PG.stack=gp pg) (RBI.si r)
               rb01 :  RBtreeInvariant (PG.grand pg)
               rb01 = PGtoRBinvariant1 _ orig (RBI.origrb r) _ (popStackInvariant _ _ _ _ _ (popStackInvariant _ _ _ _ _ rb00))
               rb02 : RBtreeInvariant (PG.uncle pg)
               rb02 = RBtreeRightDown _ _ (subst (λ k → RBtreeInvariant k) x₁ rb01)
               rb03 : RBtreeInvariant (PG.parent pg)
               rb03 = RBtreeLeftDown _ _ (subst (λ k → RBtreeInvariant k) x₁ rb01)
               rb04 : RBtreeInvariant n1
               rb04 = RBtreeRightDown _ _ (subst (λ k → RBtreeInvariant k) x rb03)
               rb05 : { tree : bt (Color ∧ A) } → tree ≡ PG.uncle pg → tree ≡ node key₁ ⟪ Red , value₁ ⟫ t₁ t₂ → color (PG.uncle pg) ≡ Red
               rb05 refl refl = refl
               rb08 : treeInvariant (PG.parent pg)
               rb08 = siToTreeinvariant _ _ _ _ (RBI.origti r) (popStackInvariant _ _ _ _ _ rb00)
               rb07 : treeInvariant (node kp vp (RBI.tree r) n1)
               rb07 = subst (λ k → treeInvariant k) x (siToTreeinvariant _ _ _ _ (RBI.origti r) (popStackInvariant _ _ _ _ _ rb00))
               rb06 : key < kp
               rb06 = lt
               rb10 : vg ≡ ⟪ Black , proj2 vg ⟫
               rb10 with RBtreeParentColorBlack _ _ (subst (λ k → RBtreeInvariant k) x₁ rb01) (case1 pcolor)
               ... | refl = refl
               rb11 : vp ≡ ⟪ Red , proj2 vp ⟫
               rb11 with subst (λ k → color k ≡ Red) x pcolor
               ... | refl = refl
               rb09 : PG.grand pg ≡ node kg ⟪ Black , proj2 vg ⟫ (node kp ⟪ Red , proj2 vp ⟫ (RBI.tree r) n1) (PG.uncle pg)
               rb09 = begin
                   PG.grand pg ≡⟨ x₁ ⟩
                   node kg vg (PG.parent pg) (PG.uncle pg) ≡⟨ cong (λ k → node kg vg k (PG.uncle pg)) x ⟩
                   node kg vg (node kp vp (RBI.tree r) n1) (PG.uncle pg) ≡⟨ cong₂ (λ j k → node kg j (node kp k (RBI.tree r) n1) (PG.uncle pg)) rb10 rb11  ⟩
                   node kg ⟪ Black , proj2 vg ⟫ (node kp ⟪ Red , proj2 vp ⟫ (RBI.tree r) n1) (PG.uncle pg) ∎
                     where open ≡-Reasoning
               rb13 : black-depth repl ≡ black-depth n1
               rb13 = begin
                  black-depth repl ≡⟨ sym (RB-repl→eq _ _ (RBI.treerb r) rot) ⟩
                  black-depth (RBI.tree r) ≡⟨ RBtreeEQ (subst (λ k → RBtreeInvariant k) x rb03) ⟩
                  black-depth n1 ∎
                     where open ≡-Reasoning
               rb12 : suc (black-depth repl ⊔ black-depth n1) ≡ black-depth (to-black (PG.uncle pg))
               rb12 = begin
                  suc (black-depth repl ⊔ black-depth n1) ≡⟨ cong (λ k → suc (k ⊔ black-depth n1)) (sym (RB-repl→eq _ _ (RBI.treerb r) rot)) ⟩
                  suc (black-depth (RBI.tree r) ⊔ black-depth n1) ≡⟨ cong (λ k → suc (k ⊔ black-depth n1)) (RBtreeEQ (subst (λ k → RBtreeInvariant k) x rb03)) ⟩
                  suc (black-depth n1 ⊔ black-depth n1) ≡⟨ ⊔-idem _ ⟩
                  suc (black-depth n1 ) ≡⟨ cong suc (sym (proj2 (red-children-eq x (cong proj1 rb11) rb03 ))) ⟩
                  suc (black-depth (PG.parent pg)) ≡⟨ cong suc (RBtreeEQ (subst (λ k → RBtreeInvariant k) x₁ rb01)) ⟩
                  suc (black-depth (PG.uncle pg)) ≡⟨ to-black-eq (PG.uncle pg) (cong color uneq ) ⟩
                  black-depth (to-black (PG.uncle pg)) ∎
                     where open ≡-Reasoning
               rb15 : suc (length (PG.rest pg)) < length stack
               rb15 = begin
                  suc (suc (length (PG.rest pg))) ≤⟨ <-trans (n<1+n _) (n<1+n _) ⟩
                  length (RBI.tree r ∷ PG.parent pg ∷ PG.grand pg ∷ PG.rest pg) ≡⟨ cong length (sym (PG.stack=gp pg)) ⟩
                  length stack ∎
                     where open ≤-Reasoning
               rb20 = (subst₂ (λ j k → replacedRBTree key value j k ) (sym rb09) refl (rbr-flip-ll repl-red (rb05 refl uneq) rb06 rot))
    ... | s2-1sp2 {kp} {kg} {vp} {vg} {n1} {n2} lt lt2 x x₁ = insertCase2 where
        insertCase2 : t
        insertCase2 = next  (PG.grand pg ∷ (PG.rest pg))
            record {
                 tree = PG.grand pg
                 ; repl = to-red (node kg vg (to-black (node kp vp n1 repl)) (to-black (PG.uncle pg))  )
                 ; origti = RBI.origti r
                 ; origrb = RBI.origrb r
                 ; treerb = rb01
                 ; replrb = rb-red _ _ refl (RBtreeToBlackColor _ rb02) rb12 (rb-black _ _ (sym rb13) rb04 (RBI.replrb r)) (RBtreeToBlack _ rb02)
                 ; replti = RB-repl→ti _ _ _ _  (siToTreeinvariant _ _ _ _ (RBI.origti r) (popStackInvariant _ _ _ _ _ (popStackInvariant _ _ _ _ _ rb00))) rb20
                 ; si = popStackInvariant _ _ _ _ _ (popStackInvariant _ _ _ _ _ rb00)
                 ; state = rotate _ refl (subst₂ (λ j k → replacedRBTree key value j k ) rb09 refl (rbr-flip-lr repl-red (rb05 refl uneq) rb06 rb21 rot))
             }  rb15 where
               --
               -- lt       : kp < key
               --  x       : PG.parent pg ≡ node kp vp n1 (RBI.tree r)
               --- x₁      : PG.grand pg ≡ node kg vg (PG.parent pg) (PG.uncle pg)
               --
               rb00 : stackInvariant key (RBI.tree r) orig (RBI.tree r ∷ PG.parent pg ∷ PG.grand pg ∷ PG.rest pg)
               rb00 = subst (λ k → stackInvariant key (RBI.tree r) orig k) (PG.stack=gp pg) (RBI.si r)
               rb01 : RBtreeInvariant (PG.grand pg)
               rb01 = PGtoRBinvariant1 _ orig (RBI.origrb r) _ (popStackInvariant _ _ _ _ _ (popStackInvariant _ _ _ _ _ rb00))
               rb02 : RBtreeInvariant (PG.uncle pg)
               rb02 = RBtreeRightDown _ _ (subst (λ k → RBtreeInvariant k) x₁ rb01)
               rb03 : RBtreeInvariant (PG.parent pg)
               rb03 = RBtreeLeftDown _ _ (subst (λ k → RBtreeInvariant k) x₁ rb01)
               rb04 : RBtreeInvariant n1
               rb04 = RBtreeLeftDown _ _ (subst (λ k → RBtreeInvariant k) x rb03)
               rb05 : { tree : bt (Color ∧ A) } → tree ≡ PG.uncle pg → tree ≡ node key₁ ⟪ Red , value₁ ⟫ t₁ t₂ → color (PG.uncle pg) ≡ Red
               rb05 refl refl = refl
               rb08 : treeInvariant (PG.parent pg)
               rb08 = siToTreeinvariant _ _ _ _ (RBI.origti r) (popStackInvariant _ _ _ _ _ rb00)
               rb07 : treeInvariant (node kp vp n1 (RBI.tree r) )
               rb07 = subst (λ k → treeInvariant k) x (siToTreeinvariant _ _ _ _ (RBI.origti r) (popStackInvariant _ _ _ _ _ rb00))
               rb06 : kp < key
               rb06 = lt
               rb21 : key < kg   -- this can be a part of ParentGand relation
               rb21 = si-property-< (subst (λ k → ¬ (k ≡ leaf)) (sym x) (λ ())) (subst (λ k → treeInvariant k ) x₁ (siToTreeinvariant _ _ _ _ (RBI.origti r)
                     (popStackInvariant _ _ _ _ _ (popStackInvariant _ _ _ _ _ rb00))))
                     (subst (λ k → stackInvariant key _ orig (PG.parent pg ∷ k ∷ PG.rest pg)) x₁ (popStackInvariant _ _ _ _ _ rb00))
               rb10 : vg ≡ ⟪ Black , proj2 vg ⟫
               rb10 with RBtreeParentColorBlack _ _ (subst (λ k → RBtreeInvariant k) x₁ rb01) (case1 pcolor)
               ... | refl = refl
               rb11 : vp ≡ ⟪ Red , proj2 vp ⟫
               rb11 with subst (λ k → color k ≡ Red) x pcolor
               ... | refl = refl
               rb09 : node kg ⟪ Black , proj2 vg ⟫  (node kp ⟪ Red , proj2 vp ⟫ n1 (RBI.tree r) ) (PG.uncle pg) ≡ PG.grand pg
               rb09 = sym ( begin
                   PG.grand pg ≡⟨ x₁ ⟩
                   node kg vg  (PG.parent pg) (PG.uncle pg) ≡⟨ cong (λ k → node kg vg k (PG.uncle pg)) x ⟩
                   node kg vg  (node kp vp n1 (RBI.tree r) ) (PG.uncle pg)  ≡⟨ cong₂ (λ j k → node kg j  (node kp k n1 (RBI.tree r) ) (PG.uncle pg) ) rb10 rb11  ⟩
                   node kg ⟪ Black , proj2 vg ⟫ (node kp ⟪ Red , proj2 vp ⟫ n1 (RBI.tree r) ) (PG.uncle pg) ∎ )
                     where open ≡-Reasoning
               rb13 : black-depth repl ≡ black-depth n1
               rb13 = begin
                  black-depth repl ≡⟨ sym (RB-repl→eq _ _ (RBI.treerb r) rot) ⟩
                  black-depth (RBI.tree r) ≡⟨ sym (RBtreeEQ (subst (λ k → RBtreeInvariant k) x rb03)) ⟩
                  black-depth n1 ∎
                     where open ≡-Reasoning
               rb12 : suc (black-depth n1 ⊔ black-depth repl) ≡ black-depth (to-black (PG.uncle pg))
               rb12 = begin
                  suc (black-depth n1 ⊔ black-depth repl) ≡⟨ cong (λ k → suc (black-depth n1 ⊔ k)) (sym (RB-repl→eq _ _ (RBI.treerb r) rot)) ⟩
                  suc (black-depth n1 ⊔ black-depth (RBI.tree r)) ≡⟨ cong (λ k → suc (black-depth n1 ⊔ k)) (sym (RBtreeEQ (subst (λ k → RBtreeInvariant k) x rb03))) ⟩
                  suc (black-depth n1 ⊔ black-depth n1) ≡⟨ ⊔-idem _ ⟩
                  suc (black-depth n1 ) ≡⟨ cong suc (sym (proj1 (red-children-eq x (cong proj1 rb11) rb03 ))) ⟩
                  suc (black-depth (PG.parent pg)) ≡⟨ cong suc (RBtreeEQ (subst (λ k → RBtreeInvariant k) x₁ rb01)) ⟩
                  suc (black-depth (PG.uncle pg)) ≡⟨ to-black-eq (PG.uncle pg) (cong color uneq ) ⟩
                  black-depth (to-black (PG.uncle pg)) ∎
                     where open ≡-Reasoning
               rb15 : suc (length (PG.rest pg)) < length stack
               rb15 = begin
                  suc (suc (length (PG.rest pg))) ≤⟨ <-trans (n<1+n _) (n<1+n _) ⟩
                  length (RBI.tree r ∷ PG.parent pg ∷ PG.grand pg ∷ PG.rest pg) ≡⟨ cong length (sym (PG.stack=gp pg)) ⟩
                  length stack ∎
                     where open ≤-Reasoning
               rb20 = subst₂ (λ j k → replacedRBTree key value j k ) rb09 refl (rbr-flip-lr repl-red (rb05 refl uneq) rb06 rb21 rot)
    ... | s2-s12p {kp} {kg} {vp} {vg} {n1} {n2} lt lt2 x x₁ = insertCase2 where
        insertCase2 : t
        insertCase2 = next  (PG.grand pg ∷ (PG.rest pg))
            record {
                 tree = PG.grand pg
                 ; repl = to-red (node kg vg (to-black (PG.uncle pg)) (to-black (node kp vp repl n1)) )
                 ; origti = RBI.origti r
                 ; origrb = RBI.origrb r
                 ; treerb = rb01
                 ; si = popStackInvariant _ _ _ _ _ (popStackInvariant _ _ _ _ _ rb00)
                 ; replrb = rb-red _ _ (RBtreeToBlackColor _ rb02) refl rb12 (RBtreeToBlack _ rb02) (rb-black _ _ rb13 (RBI.replrb r) rb04)
                 ; replti = RB-repl→ti _ _ _ _  (siToTreeinvariant _ _ _ _ (RBI.origti r) (popStackInvariant _ _ _ _ _ (popStackInvariant _ _ _ _ _ rb00))) rb20
                 ; state = rotate _ refl (subst₂ (λ j k → replacedRBTree key value j k ) rb09 refl  (rbr-flip-rl repl-red (rb05 refl uneq) rb21 rb06 rot))
             }  rb15 where
                 -- x   : PG.parent pg ≡ node kp vp (RBI.tree r) n1
                 -- x₁  : PG.grand pg ≡ node kg vg (PG.uncle pg) (PG.parent pg)
               rb00 : stackInvariant key (RBI.tree r) orig (RBI.tree r ∷ PG.parent pg ∷ PG.grand pg ∷ PG.rest pg)
               rb00 = subst (λ k → stackInvariant key (RBI.tree r) orig k) (PG.stack=gp pg) (RBI.si r)
               rb01 :  RBtreeInvariant (PG.grand pg)
               rb01 = PGtoRBinvariant1 _ orig (RBI.origrb r) _ (popStackInvariant _ _ _ _ _ (popStackInvariant _ _ _ _ _ rb00))
               rb02 : RBtreeInvariant (PG.uncle pg)
               rb02 = RBtreeLeftDown _ _ (subst (λ k → RBtreeInvariant k) x₁ rb01)
               rb03 : RBtreeInvariant (PG.parent pg)
               rb03 = RBtreeRightDown _ _ (subst (λ k → RBtreeInvariant k) x₁ rb01)
               rb04 : RBtreeInvariant n1
               rb04 = RBtreeRightDown _ _ (subst (λ k → RBtreeInvariant k) x rb03)
               rb05 : { tree : bt (Color ∧ A) } → tree ≡ PG.uncle pg → tree ≡ node key₁ ⟪ Red , value₁ ⟫ t₁ t₂ → color (PG.uncle pg) ≡ Red
               rb05 refl refl = refl
               rb08 : treeInvariant (PG.parent pg)
               rb08 = siToTreeinvariant _ _ _ _ (RBI.origti r) (popStackInvariant _ _ _ _ _ rb00)
               rb07 : treeInvariant (node kp vp (RBI.tree r) n1)
               rb07 = subst (λ k → treeInvariant k) x (siToTreeinvariant _ _ _ _ (RBI.origti r) (popStackInvariant _ _ _ _ _ rb00))
               rb06 : key < kp
               rb06 = lt
               rb21 : kg < key   -- this can be a part of ParentGand relation
               rb21 = si-property-> (subst (λ k → ¬ (k ≡ leaf)) (sym x) (λ ())) (subst (λ k → treeInvariant k ) x₁ (siToTreeinvariant _ _ _ _ (RBI.origti r)
                     (popStackInvariant _ _ _ _ _ (popStackInvariant _ _ _ _ _ rb00))))
                     (subst (λ k → stackInvariant key _ orig (PG.parent pg ∷ k ∷ PG.rest pg)) x₁ (popStackInvariant _ _ _ _ _ rb00))
               rb10 : vg ≡ ⟪ Black , proj2 vg ⟫
               rb10 with RBtreeParentColorBlack _ _ (subst (λ k → RBtreeInvariant k) x₁ rb01) (case2 pcolor)
               ... | refl = refl
               rb11 : vp ≡ ⟪ Red , proj2 vp ⟫
               rb11 with subst (λ k → color k ≡ Red) x pcolor
               ... | refl = refl
               rb09 : node kg ⟪ Black , proj2 vg ⟫ (PG.uncle pg) (node kp ⟪ Red , proj2 vp ⟫ (RBI.tree r) n1) ≡ PG.grand pg
               rb09 = sym ( begin
                   PG.grand pg ≡⟨ x₁ ⟩
                   node kg vg (PG.uncle pg) (PG.parent pg)  ≡⟨ cong (λ k → node kg vg (PG.uncle pg) k) x ⟩
                   node kg vg (PG.uncle pg) (node kp vp (RBI.tree r) n1)  ≡⟨ cong₂ (λ j k → node kg j (PG.uncle pg) (node kp k (RBI.tree r) n1) ) rb10 rb11  ⟩
                   node kg ⟪ Black , proj2 vg ⟫ (PG.uncle pg) (node kp ⟪ Red , proj2 vp ⟫ (RBI.tree r) n1) ∎ )
                     where open ≡-Reasoning
               rb13 : black-depth repl ≡ black-depth n1
               rb13 = begin
                  black-depth repl ≡⟨ sym (RB-repl→eq _ _ (RBI.treerb r) rot) ⟩
                  black-depth (RBI.tree r) ≡⟨ RBtreeEQ (subst (λ k → RBtreeInvariant k) x rb03) ⟩
                  black-depth n1 ∎
                     where open ≡-Reasoning
               -- rb12 : suc (black-depth repl ⊔ black-depth n1) ≡ black-depth (to-black (PG.uncle pg))
               rb12 : black-depth (to-black (PG.uncle pg)) ≡ suc (black-depth repl ⊔ black-depth n1)
               rb12 = sym ( begin
                  suc (black-depth repl ⊔ black-depth n1) ≡⟨ cong (λ k → suc (k ⊔ black-depth n1)) (sym (RB-repl→eq _ _ (RBI.treerb r) rot)) ⟩
                  suc (black-depth (RBI.tree r) ⊔ black-depth n1) ≡⟨ cong (λ k → suc (k ⊔ black-depth n1)) (RBtreeEQ (subst (λ k → RBtreeInvariant k) x rb03)) ⟩
                  suc (black-depth n1 ⊔ black-depth n1) ≡⟨ ⊔-idem _ ⟩
                  suc (black-depth n1 ) ≡⟨ cong suc (sym (proj2 (red-children-eq x (cong proj1 rb11) rb03 ))) ⟩
                  suc (black-depth (PG.parent pg)) ≡⟨ cong suc (sym (RBtreeEQ (subst (λ k → RBtreeInvariant k) x₁ rb01))) ⟩
                  suc (black-depth (PG.uncle pg)) ≡⟨ to-black-eq (PG.uncle pg) (cong color uneq ) ⟩
                  black-depth (to-black (PG.uncle pg)) ∎ )
                     where open ≡-Reasoning
               rb17 : suc (black-depth repl ⊔ black-depth n1) ⊔ black-depth (to-black (PG.uncle pg)) ≡ black-depth (PG.grand pg)
               rb17 = begin
                  suc (black-depth repl ⊔ black-depth n1) ⊔ black-depth (to-black (PG.uncle pg)) ≡⟨ cong (λ k → k ⊔ black-depth (to-black (PG.uncle pg))) (sym rb12) ⟩
                  black-depth (to-black (PG.uncle pg)) ⊔ black-depth (to-black (PG.uncle pg)) ≡⟨ ⊔-idem _ ⟩
                  black-depth (to-black (PG.uncle pg)) ≡⟨ sym (to-black-eq (PG.uncle pg) (cong color uneq )) ⟩
                  suc (black-depth (PG.uncle pg)) ≡⟨ sym ( proj1 (black-children-eq x₁ (cong proj1 rb10) rb01 )) ⟩
                  black-depth (PG.grand pg) ∎
                     where open ≡-Reasoning
               rb15 : suc (length (PG.rest pg)) < length stack
               rb15 = begin
                  suc (suc (length (PG.rest pg))) ≤⟨ <-trans (n<1+n _) (n<1+n _) ⟩
                  length (RBI.tree r ∷ PG.parent pg ∷ PG.grand pg ∷ PG.rest pg) ≡⟨ cong length (sym (PG.stack=gp pg)) ⟩
                  length stack ∎
                     where open ≤-Reasoning
               rb20 = subst₂ (λ j k → replacedRBTree key value j k ) rb09 refl  (rbr-flip-rl repl-red (rb05 refl uneq) rb21 rb06 rot)
    ... | s2-1s2p {kp} {kg} {vp} {vg} {n1} {n2} lt lt2 x x₁ = insertCase2 where
           --- lt : kp < key
           --- x  : PG.parent pg ≡ node kp vp n1 (RBI.tree r)
           --- x₁ : PG.grand pg ≡ node kg vg (PG.uncle pg) (PG.parent pg)
        insertCase2 : t
        insertCase2 = next  (PG.grand pg ∷ (PG.rest pg))
            record {
                 tree = PG.grand pg
                 ; repl = to-red (node kg vg (to-black (PG.uncle pg)) (to-black (node kp vp n1 repl )) )
                 ; origti = RBI.origti r
                 ; origrb = RBI.origrb r
                 ; treerb = rb01
                 ; replrb = rb-red _ _ (RBtreeToBlackColor _ rb02) refl rb12  (RBtreeToBlack _ rb02) (rb-black _ _ (sym rb13) rb04 (RBI.replrb r) )
                 ; replti = RB-repl→ti _ _ _ _  (siToTreeinvariant _ _ _ _ (RBI.origti r) (popStackInvariant _ _ _ _ _ (popStackInvariant _ _ _ _ _ rb00))) rb20
                 ; si = popStackInvariant _ _ _ _ _ (popStackInvariant _ _ _ _ _ rb00)
                 ; state = rotate _ refl (subst₂ (λ j k → replacedRBTree key value j k ) (sym rb09) refl  (rbr-flip-rr repl-red (rb05 refl uneq) rb06 rot))
             }  rb15 where
               rb00 : stackInvariant key (RBI.tree r) orig (RBI.tree r ∷ PG.parent pg ∷ PG.grand pg ∷ PG.rest pg)
               rb00 = subst (λ k → stackInvariant key (RBI.tree r) orig k) (PG.stack=gp pg) (RBI.si r)
               rb01 :  RBtreeInvariant (PG.grand pg)
               rb01 = PGtoRBinvariant1 _ orig (RBI.origrb r) _ (popStackInvariant _ _ _ _ _ (popStackInvariant _ _ _ _ _ rb00))
               rb02 : RBtreeInvariant (PG.uncle pg)
               rb02 = RBtreeLeftDown _ _ (subst (λ k → RBtreeInvariant k) x₁ rb01)
               rb03 : RBtreeInvariant (PG.parent pg)
               rb03 = RBtreeRightDown _ _ (subst (λ k → RBtreeInvariant k) x₁ rb01)
               rb04 : RBtreeInvariant n1
               rb04 = RBtreeLeftDown _ _ (subst (λ k → RBtreeInvariant k) x rb03)
               rb05 : { tree : bt (Color ∧ A) } → tree ≡ PG.uncle pg → tree ≡ node key₁ ⟪ Red , value₁ ⟫ t₁ t₂ → color (PG.uncle pg) ≡ Red
               rb05 refl refl = refl
               rb08 : treeInvariant (PG.parent pg)
               rb08 = siToTreeinvariant _ _ _ _ (RBI.origti r) (popStackInvariant _ _ _ _ _ rb00)
               rb07 : treeInvariant (node kp vp n1 (RBI.tree r) )
               rb07 = subst (λ k → treeInvariant k) x (siToTreeinvariant _ _ _ _ (RBI.origti r) (popStackInvariant _ _ _ _ _ rb00))
               rb06 : kp < key
               rb06 = lt
               rb10 : vg ≡ ⟪ Black , proj2 vg ⟫
               rb10 with RBtreeParentColorBlack _ _ (subst (λ k → RBtreeInvariant k) x₁ rb01) (case2 pcolor)
               ... | refl = refl
               rb11 : vp ≡ ⟪ Red , proj2 vp ⟫
               rb11 with subst (λ k → color k ≡ Red) x pcolor
               ... | refl = refl
               rb09 : PG.grand pg ≡ node kg ⟪ Black , proj2 vg ⟫ (PG.uncle pg) (node kp ⟪ Red , proj2 vp ⟫ n1 (RBI.tree r) )
               rb09 = begin
                   PG.grand pg ≡⟨ x₁ ⟩
                   node kg vg (PG.uncle pg) (PG.parent pg) ≡⟨ cong (λ k → node kg vg (PG.uncle pg) k) x ⟩
                   node kg vg (PG.uncle pg) (node kp vp n1 (RBI.tree r) )  ≡⟨ cong₂ (λ j k → node kg j (PG.uncle pg) (node kp k n1 (RBI.tree r) ) ) rb10 rb11  ⟩
                   node kg ⟪ Black , proj2 vg ⟫ (PG.uncle pg) (node kp ⟪ Red , proj2 vp ⟫ n1 (RBI.tree r) )  ∎
                     where open ≡-Reasoning
               rb13 : black-depth repl ≡ black-depth n1
               rb13 = begin
                  black-depth repl ≡⟨ sym (RB-repl→eq _ _ (RBI.treerb r) rot) ⟩
                  black-depth (RBI.tree r) ≡⟨ sym (RBtreeEQ (subst (λ k → RBtreeInvariant k) x rb03)) ⟩
                  black-depth n1 ∎
                     where open ≡-Reasoning
               rb12 : black-depth (to-black (PG.uncle pg)) ≡ suc (black-depth n1 ⊔ black-depth repl)
               rb12 = sym ( begin
                  suc (black-depth n1 ⊔ black-depth repl) ≡⟨ cong suc (⊔-comm (black-depth n1) _) ⟩
                  suc (black-depth repl ⊔ black-depth n1) ≡⟨ cong (λ k → suc (k ⊔ black-depth n1)) (sym (RB-repl→eq _ _ (RBI.treerb r) rot)) ⟩
                  suc (black-depth (RBI.tree r) ⊔ black-depth n1) ≡⟨ cong (λ k → suc (k ⊔ black-depth n1)) (sym (RBtreeEQ (subst (λ k → RBtreeInvariant k) x rb03))) ⟩
                  suc (black-depth n1 ⊔ black-depth n1) ≡⟨ ⊔-idem _ ⟩
                  suc (black-depth n1 ) ≡⟨ cong suc (sym (proj1 (red-children-eq x (cong proj1 rb11) rb03 ))) ⟩
                  suc (black-depth (PG.parent pg)) ≡⟨ cong suc (sym (RBtreeEQ (subst (λ k → RBtreeInvariant k) x₁ rb01))) ⟩
                  suc (black-depth (PG.uncle pg)) ≡⟨ to-black-eq (PG.uncle pg) (cong color uneq ) ⟩
                  black-depth (to-black (PG.uncle pg)) ∎ )
                     where open ≡-Reasoning
               rb15 : suc (length (PG.rest pg)) < length stack
               rb15 = begin
                  suc (suc (length (PG.rest pg))) ≤⟨ <-trans (n<1+n _) (n<1+n _) ⟩
                  length (RBI.tree r ∷ PG.parent pg ∷ PG.grand pg ∷ PG.rest pg) ≡⟨ cong length (sym (PG.stack=gp pg)) ⟩
                  length stack ∎
                     where open ≤-Reasoning
               rb20 = subst₂ (λ j k → replacedRBTree key value j k ) (sym rb09) refl  (rbr-flip-rr repl-red (rb05 refl uneq) rb06 rot)



insertRBTreeP : {n m : Level} {A : Set n} {t : Set m} → (tree : bt (Color ∧ A)) → (key : ℕ) → (value : A)
   → treeInvariant tree → RBtreeInvariant tree
   → (exit : (stack  : List (bt (Color ∧ A))) → stack ≡ (tree ∷ []) → RBI key value tree stack → t ) → t
insertRBTreeP {n} {m} {A} {t} orig key value ti rbi exit = TerminatingLoopS (bt (Color ∧ A) ∧ List (bt (Color ∧ A)))
 {λ p → RBtreeInvariant (proj1 p) ∧ stackInvariant key (proj1 p) orig (proj2 p) } (λ p → bt-depth (proj1 p)) ⟪ orig , orig ∷ [] ⟫ ⟪ rbi , s-nil ⟫
       $ λ p RBP findLoop → findRBT key (proj1 p) orig (proj2 p) RBP  (λ t1 s1 P2 lt1 → findLoop ⟪ t1 ,  s1  ⟫ P2 lt1 )
       $ λ tr1 st P2 O → createRBT key value orig rbi ti tr1 st (proj2 P2) O
       $ λ st rbi → TerminatingLoopS (List (bt (Color ∧ A))) {λ stack → RBI key value orig stack }
          (λ stack  → length stack ) st rbi
            $ λ stack rbi replaceLoop → replaceRBP key value orig stack rbi (λ stack1 rbi1 lt → replaceLoop stack1 rbi1 lt )
            $ λ stack eq r → exit stack eq r


insertRBTestP1 = insertRBTreeP leaf 1 1 t-leaf rb-leaf
   $ λ _ x0 P0 → insertRBTreeP (RBI.repl P0) 2 1 (RBI.replti P0) (RBI.replrb P0)
   $ λ _ x0 P0 → insertRBTreeP (RBI.repl P0) 3 2 (RBI.replti P0) (RBI.replrb P0)
   $ λ _ x0 P0 → insertRBTreeP (RBI.repl P0) 2 2 (RBI.replti P0) (RBI.replrb P0)
   $ λ _ x P  → RBI.repl P0

