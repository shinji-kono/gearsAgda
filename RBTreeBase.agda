{-# OPTIONS --cubical-compatible --safe #-}
module RBTreeBase where

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

open _∧_

data Color  : Set where
    Red : Color
    Black : Color

RB→bt : {n : Level} (A : Set n) → (bt (Color ∧ A)) → bt A
RB→bt {n} A leaf = leaf
RB→bt {n} A (node key ⟪ C , value ⟫ tr t1) = (node key value (RB→bt A tr) (RB→bt A t1))

color : {n : Level} {A : Set n} → (bt (Color ∧ A)) → Color
color leaf = Black
color (node key ⟪ C , value ⟫ rb rb₁) = C

to-red : {n : Level} {A : Set n} → (tree : bt (Color ∧ A)) → bt (Color ∧ A)
to-red leaf = leaf
to-red (node key ⟪ _ , value ⟫ t t₁) = (node key ⟪ Red , value ⟫ t t₁)

to-black : {n : Level} {A : Set n} → (tree : bt (Color ∧ A)) → bt (Color ∧ A)
to-black leaf = leaf
to-black (node key ⟪ _ , value ⟫ t t₁) = (node key ⟪ Black , value ⟫ t t₁)

black-depth : {n : Level} {A : Set n} → (tree : bt (Color ∧ A) ) → ℕ
black-depth leaf = 1
black-depth (node key ⟪ Red , value ⟫  t t₁) = black-depth t  ⊔ black-depth t₁
black-depth (node key ⟪ Black , value ⟫  t t₁) = suc (black-depth t  ⊔ black-depth t₁ )

zero≢suc : { m : ℕ } → zero ≡ suc m → ⊥
zero≢suc ()
suc≢zero : {m : ℕ } → suc m ≡ zero → ⊥
suc≢zero ()

data RBtreeInvariant {n : Level} {A : Set n} : (tree : bt (Color ∧ A)) → Set n where
    rb-leaf :  RBtreeInvariant leaf
    rb-red :  (key : ℕ) → (value : A) → {left right : bt (Color ∧ A)}
       → color left ≡ Black → color right ≡ Black
       → black-depth left ≡ black-depth right
       → RBtreeInvariant left → RBtreeInvariant right
       → RBtreeInvariant (node key ⟪ Red , value ⟫ left right)
    rb-black :  (key : ℕ) → (value : A) → {left right : bt (Color ∧ A)}
       → black-depth left ≡ black-depth right
       → RBtreeInvariant left → RBtreeInvariant right
       → RBtreeInvariant (node key ⟪ Black , value ⟫ left right)

RightDown : {n : Level} {A : Set n} → bt (Color ∧ A) → bt (Color ∧ A)
RightDown leaf = leaf
RightDown (node key ⟪ c , value ⟫ t1 t2) = t2
LeftDown : {n : Level} {A :  Set n} → bt (Color ∧ A) → bt (Color ∧ A)
LeftDown leaf = leaf
LeftDown (node key ⟪ c , value ⟫ t1 t2 ) = t1

RBtreeLeftDown : {n : Level} {A : Set n} {key : ℕ} {value : A} {c : Color}
 →  (left right : bt (Color ∧ A))
 → RBtreeInvariant (node key ⟪ c , value ⟫ left right)
 → RBtreeInvariant left
RBtreeLeftDown {n} {A} {key} {value} {c} left right rb = lem00 _ rb refl where
    lem00 : (tree : bt (Color ∧ A) ) → ( rb : RBtreeInvariant tree ) → tree ≡ node key ⟪ c , value ⟫ left right → RBtreeInvariant left
    lem00 _ rb-leaf ()
    lem00 (node key ⟪ c , value ⟫ _ _) (rb-red key value x x₁ x₂ rb rb₁) eq = subst (λ k → RBtreeInvariant k) (just-injective (cong node-left eq)) rb
    lem00 (node key ⟪ c , value ⟫ _ _) (rb-black key value x rb rb₁) eq = subst (λ k → RBtreeInvariant k) (just-injective (cong node-left eq)) rb


RBtreeRightDown : {n : Level} {A : Set n} { key : ℕ} {value : A} {c : Color}
 → (left right : bt (Color ∧ A))
 → RBtreeInvariant (node key ⟪ c , value ⟫ left right)
 → RBtreeInvariant right
RBtreeRightDown {n} {A} {key} {value} {c} left right rb = lem00 _ rb refl where
    lem00 : (tree : bt (Color ∧ A) ) → ( rb : RBtreeInvariant tree ) → tree ≡ node key ⟪ c , value ⟫ left right → RBtreeInvariant right
    lem00 _ rb-leaf ()
    lem00 (node key ⟪ c , value ⟫ _ _) (rb-red key value x x₁ x₂ rb rb₁) eq = subst (λ k → RBtreeInvariant k) (just-injective (cong node-right eq)) rb₁
    lem00 (node key ⟪ c , value ⟫ _ _) (rb-black key value x rb rb₁) eq = subst (λ k → RBtreeInvariant k) (just-injective (cong node-right eq)) rb₁

RBtreeEQ : {n : Level} {A : Set n} {key : ℕ} {value : A} {c : Color}
 → {left right : bt (Color ∧ A)}
 → RBtreeInvariant (node key ⟪ c , value ⟫ left right)
 → black-depth left ≡ black-depth right
RBtreeEQ {n} {A} {key} {value} {c} {left} {right} rb = lem00 _ rb refl where
    lem00 : (tree : bt (Color ∧ A) ) → ( rb : RBtreeInvariant tree ) → tree ≡ node key ⟪ c , value ⟫ left right → black-depth left ≡ black-depth right
    lem00 _ rb-leaf ()
    lem00 (node key ⟪ c , value ⟫ _ _) (rb-red key value x x₁ x₂ rb rb₁) eq
       = subst₂ (λ k l → black-depth k ≡ black-depth l) (just-injective (cong node-left eq)) (just-injective (cong node-right eq)) x₂
    lem00 (node key ⟪ c , value ⟫ _ _) (rb-black key value x rb rb₁) eq
       = subst₂ (λ k l → black-depth k ≡ black-depth l) (just-injective (cong node-left eq)) (just-injective (cong node-right eq)) x

RBtreeToBlack : {n : Level} {A : Set n}
 → (tree : bt (Color ∧ A))
 → RBtreeInvariant tree
 → RBtreeInvariant (to-black tree)
RBtreeToBlack {n} {A} tree rb = lem00 _ rb where
    lem00 : (tree : bt (Color ∧ A) ) → ( rb : RBtreeInvariant tree ) → RBtreeInvariant (to-black tree)
    lem00 _ rb-leaf = rb-leaf
    lem00 (node key ⟪ c , value ⟫ left right) (rb-red key value x x₁ x₂ rb rb₁) = rb-black key value x₂ rb rb₁
    lem00 (node key ⟪ c , value ⟫ left right) (rb-black key value x rb rb₁) = rb-black key value x rb rb₁

RBtreeToBlackColor : {n : Level} {A : Set n}
 → (tree : bt (Color ∧ A))
 → RBtreeInvariant tree
 → color (to-black tree) ≡ Black
RBtreeToBlackColor {n} {A} _ rb-leaf = refl
RBtreeToBlackColor {n} {A} (node key ⟪ c , value ⟫ left right) (rb-red key value x x₁ x₂ rb rb₁) = refl
RBtreeToBlackColor {n} {A} (node key ⟪ c , value ⟫ left right) (rb-black key value x rb rb₁) = refl

⊥-color : ( Black ≡ Red ) → ⊥
⊥-color ()

RBtreeParentColorBlack : {n : Level} {A : Set n} → (left right  : bt (Color ∧ A)) { value : A} {key : ℕ} { c : Color}
 → RBtreeInvariant (node key ⟪ c , value ⟫ left right)
 → (color left ≡ Red) ∨ (color right ≡ Red)
 → c ≡ Black
RBtreeParentColorBlack {n} {A} left right {value} {key} {c} rb = lem00 _ rb refl where
    lem00 : (tree : bt (Color ∧ A) ) → {c1 : Color } → ( rb : RBtreeInvariant tree )
        → (node key ⟪ c1 , value ⟫ left right ≡ tree) →  (color left ≡ Red) ∨ (color right ≡ Red) → c1 ≡ Black
    lem00 _ rb-leaf ()
    lem00 (node key ⟪ .Red , value ⟫ _ _) (rb-red key value x x₁ x₂ rb rb₁) eq (case1 left-red)
        = ⊥-elim (⊥-color (sym (trans (trans (sym left-red) (cong color (just-injective (cong node-left eq)))) x)))
    lem00 (node key ⟪ .Red , value ⟫ _ _) (rb-red key value x x₁ x₂ rb rb₁) eq (case2 right-red)
        = ⊥-elim (⊥-color (sym (trans (trans (sym right-red) (cong color (just-injective (cong node-right eq)))) x₁ )))
    lem00 (node key ⟪ c , value ⟫ _ _) (rb-black key value x rb rb₁) eq p = cong color eq

RBtreeChildrenColorBlack : {n : Level} {A : Set n} → (left right  : bt (Color ∧ A)) { value : Color ∧ A} {key : ℕ}
 → RBtreeInvariant (node key value left right)
 → proj1 value  ≡ Red
 → (color left ≡ Black) ∧  (color right ≡ Black)
RBtreeChildrenColorBlack {n} {A} left right {value} {key} br pv=r = lem00 _ br refl where
    lem00 : (tree : bt (Color ∧ A) ) → ( rb : RBtreeInvariant tree ) → tree ≡ node key value left right → (color left ≡ Black) ∧  (color right ≡ Black)
    lem00 _ rb-leaf ()
    lem00 (node key value _ _) (rb-red key value₁ x x₁ x₂ rb rb₁) eq = ⟪ trans (sym (cong color (just-injective (cong node-left eq)))) x
       , trans (sym (cong color (just-injective (cong node-right eq)))) x₁ ⟫
    lem00 (node key value _ _) (rb-black key value₁ x rb rb₁) eq = ⊥-elim ( ⊥-color (sym (trans (sym pv=r) (cong proj1 (sym (just-injective (cong node-value eq)))))))


-- create replaceRBTree with rotate

data replacedRBTree  {n : Level} {A : Set n} (key : ℕ) (value : A)  : (before after : bt (Color ∧ A) ) → Set n where
    -- no rotation case
    rbr-leaf : replacedRBTree key value leaf (node key ⟪ Red , value ⟫ leaf leaf)
    rbr-node : {value₁ : A} → {ca : Color } → {t t₁ : bt (Color ∧ A)}
          → replacedRBTree key value (node key ⟪ ca , value₁ ⟫ t t₁) (node key ⟪ ca , value ⟫ t t₁)
    rbr-right : {k : ℕ } {v1 : A} → {ca : Color} → {t t1 t2 : bt (Color ∧ A)}
          → color t2 ≡ color t
          → k < key →  replacedRBTree key value t2 t →  replacedRBTree key value (node k ⟪ ca , v1 ⟫ t1 t2) (node k ⟪ ca , v1 ⟫ t1 t)
    rbr-left  : {k : ℕ } {v1 : A} → {ca : Color} → {t t1 t2 : bt (Color ∧ A)}
          → color t1 ≡ color t
          → key < k →  replacedRBTree key value t1 t →  replacedRBTree key value (node k ⟪ ca , v1 ⟫ t1 t2) (node k ⟪ ca , v1 ⟫ t t2) -- k < key → key < k
    -- in all other case, color of replaced node is changed from Black to Red
    -- case1 parent is black
    rbr-black-right : {t t₁ t₂ : bt (Color ∧ A)} {value₁ : A} {key₁ : ℕ}
         → color t₂ ≡ Red → key₁ < key  → replacedRBTree key value t₁ t₂
         → replacedRBTree key value (node key₁ ⟪ Black , value₁ ⟫ t t₁) (node key₁ ⟪ Black , value₁ ⟫ t t₂)
    rbr-black-left : {t t₁ t₂ : bt (Color ∧ A)} {value₁ : A} {key₁ : ℕ}
         → color t₂ ≡ Red  → key < key₁ → replacedRBTree key value t₁ t₂
         → replacedRBTree key value (node key₁ ⟪ Black , value₁ ⟫ t₁ t) (node key₁ ⟪ Black , value₁ ⟫ t₂ t)

    -- case2 both parent and uncle are red (should we check uncle color?), flip color and up
    rbr-flip-ll : {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A}
         → color t₂ ≡ Red → color uncle ≡ Red → key < kp  → replacedRBTree key value t₁ t₂
         → replacedRBTree key value (node kg ⟪ Black , vg ⟫ (node kp ⟪ Red   , vp ⟫ t₁ t)           uncle)
                                    (node kg ⟪ Red ,   vg ⟫ (node kp ⟪ Black , vp ⟫ t₂ t) (to-black uncle))
    rbr-flip-lr : {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A}
         → color t₂ ≡ Red → color uncle ≡ Red →  kp < key → key < kg   → replacedRBTree key value t₁ t₂
         → replacedRBTree key value (node kg ⟪ Black , vg ⟫ (node kp ⟪ Red   , vp ⟫ t t₁)           uncle)
                                    (node kg ⟪ Red ,   vg ⟫ (node kp ⟪ Black , vp ⟫ t t₂) (to-black uncle))
    rbr-flip-rl : {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A}
         → color t₂ ≡ Red → color uncle ≡ Red → kg < key → key < kp  → replacedRBTree key value t₁ t₂
         → replacedRBTree key value (node kg ⟪ Black , vg ⟫ uncle            (node kp ⟪ Red   , vp ⟫ t₁ t))
                                    (node kg ⟪ Red ,   vg ⟫ (to-black uncle) (node kp ⟪ Black , vp ⟫ t₂ t))
    rbr-flip-rr : {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A}
         → color t₂ ≡ Red → color uncle ≡ Red → kp < key   → replacedRBTree key value t₁ t₂
         → replacedRBTree key value (node kg ⟪ Black , vg ⟫ uncle            (node kp ⟪ Red   , vp ⟫ t t₁))
                                    (node kg ⟪ Red ,   vg ⟫ (to-black uncle) (node kp ⟪ Black , vp ⟫ t t₂))

    -- case6 the node is outer, rotate grand
    rbr-rotate-ll : {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A}
         → color t₂ ≡ Red → key < kp  → replacedRBTree key value t₁ t₂
         → replacedRBTree key value (node kg ⟪ Black , vg ⟫ (node kp ⟪ Red , vp ⟫ t₁ t)    uncle)
                                    (node kp ⟪ Black , vp ⟫ t₂                             (node kg ⟪ Red , vg ⟫ t uncle))
    rbr-rotate-rr : {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A}
         → color t₂ ≡ Red → kp < key → replacedRBTree key value t₁ t₂
         → replacedRBTree key value (node kg ⟪ Black , vg ⟫ uncle                          (node kp ⟪ Red   , vp ⟫ t t₁))
                                    (node kp ⟪ Black , vp ⟫ (node kg ⟪ Red , vg ⟫ uncle t) t₂ )
    -- case56 the node is inner, make it outer and rotate grand
    rbr-rotate-lr : {t t₁ uncle : bt (Color ∧ A)} (t₂ t₃ : bt (Color ∧ A)) (kg kp kn : ℕ) {vg vp vn : A}
         → color t₃ ≡ Black → kp < key → key < kg
         → replacedRBTree key value t₁ (node kn ⟪ Red , vn ⟫ t₂ t₃)
         → replacedRBTree key value (node kg ⟪ Black , vg ⟫ (node kp ⟪ Red , vp ⟫ t t₁)     uncle)
                                    (node kn ⟪ Black , vn ⟫ (node kp ⟪ Red , vp ⟫ t t₂)     (node kg ⟪ Red , vg ⟫ t₃ uncle))
    rbr-rotate-rl : {t t₁ uncle : bt (Color ∧ A)} (t₂ t₃ : bt (Color ∧ A)) (kg kp kn : ℕ) {vg vp vn : A}
         → color t₃ ≡ Black → kg < key → key < kp
         → replacedRBTree key value t₁ (node kn ⟪ Red , vn ⟫ t₂ t₃)
         → replacedRBTree key value (node kg ⟪ Black , vg ⟫ uncle                           (node kp ⟪ Red , vp ⟫ t₁ t))
                                    (node kn ⟪ Black , vn ⟫ (node kg ⟪ Red , vg ⟫ uncle t₂) (node kp ⟪ Red , vp ⟫ t₃ t))


--
-- Parent Grand Relation
--   should we require stack-invariant?
--

data ParentGrand {n : Level} {A : Set n} (key : ℕ) (self : bt A) : (parent uncle grand : bt A) → Set n where
    s2-s1p2 : {kp kg : ℕ} {vp vg : A} → {n1 n2 : bt A} {parent grand : bt A }
        → key < kp → key < kg → parent ≡ node kp vp self n1 → grand ≡ node kg vg parent n2 → ParentGrand key self parent n2 grand
    s2-1sp2 : {kp kg : ℕ} {vp vg : A} → {n1 n2 : bt A} {parent grand : bt A }
        → kp < key → key < kg → parent ≡ node kp vp n1 self → grand ≡ node kg vg parent n2 → ParentGrand key self parent n2 grand
    s2-s12p : {kp kg : ℕ} {vp vg : A} → {n1 n2 : bt A} {parent grand : bt A }
        → key < kp → kg < key → parent ≡ node kp vp self n1 → grand ≡ node kg vg n2 parent → ParentGrand key self parent n2 grand
    s2-1s2p : {kp kg : ℕ} {vp vg : A} → {n1 n2 : bt A} {parent grand : bt A }
        → kp < key → kg < key → parent ≡ node kp vp n1 self → grand ≡ node kg vg n2 parent → ParentGrand key self parent n2 grand

record PG {n : Level } (A : Set n) (key : ℕ) (self : bt A) (stack : List (bt A)) : Set n where
    field
       parent grand uncle : bt A
       pg : ParentGrand key self parent uncle grand
       rest : List (bt A)
       stack=gp : stack ≡ ( self ∷ parent ∷ grand ∷ rest )

--
-- RBI : Invariant on InsertCase2
--     color repl ≡ Red ∧ black-depth repl ≡ suc (black-depth tree)
--

data RBI-state  {n : Level} {A : Set n} (key : ℕ) (value : A) : (tree repl : bt (Color ∧ A) ) → (stak : List (bt (Color ∧ A))) → Set n where
   rebuild : {tree repl : bt (Color ∧ A) } {stack : List (bt (Color ∧ A))} → color tree ≡ color repl → black-depth repl ≡ black-depth tree
       → ¬ ( tree ≡ leaf)
       → (rotated : replacedRBTree key value tree repl)
       → RBI-state key value tree repl stack  -- one stage up
   rotate  : (tree : bt (Color ∧ A)) → {repl : bt (Color ∧ A) } {stack : List (bt (Color ∧ A))} → color repl ≡ Red
       → (rotated : replacedRBTree key value tree repl)
       → RBI-state key value tree repl stack  -- two stages up
   top-black : {tree repl : bt (Color ∧ A) } → {stack : List (bt (Color ∧ A))}  → stack ≡ tree ∷ []
       → (rotated : replacedRBTree key value tree repl ∨ replacedRBTree key value (to-black tree) repl)
       → RBI-state key value tree repl stack

record RBI {n : Level} {A : Set n} (key : ℕ) (value : A) (orig : bt (Color ∧ A) ) (stack : List (bt (Color ∧ A)))  : Set n where
   field
       tree repl : bt (Color ∧ A)
       origti : treeInvariant orig
       origrb : RBtreeInvariant orig
       treerb : RBtreeInvariant tree     -- tree node te be replaced
       replrb : RBtreeInvariant repl
       replti : treeInvariant repl
       si : stackInvariant key tree orig stack
       state : RBI-state key value tree repl stack

tr>-to-black : {n : Level} {A : Set n} {key : ℕ} {tree : bt (Color ∧ A)} → tr> key tree → tr> key (to-black tree)
tr>-to-black {n} {A} {key} {leaf} tr = tt
tr>-to-black {n} {A} {key} {node key₁ value tree tree₁} tr = tr


tr<-to-black : {n : Level} {A : Set n} {key : ℕ} {tree : bt (Color ∧ A)} → tr< key tree → tr< key (to-black tree)
tr<-to-black {n} {A} {key} {leaf} tr = tt
tr<-to-black {n} {A} {key} {node key₁ value tree tree₁} tr = tr

to-black-eq : {n : Level} {A : Set n}  (tree : bt (Color ∧ A)) → color tree ≡ Red → suc (black-depth tree) ≡ black-depth (to-black tree)
to-black-eq {n} {A}  (leaf) ()
to-black-eq {n} {A}  (node key₁ ⟪ Red , proj4 ⟫ tree tree₁) eq = refl
to-black-eq {n} {A}  (node key₁ ⟪ Black , proj4 ⟫ tree tree₁) ()

red-children-eq : {n : Level} {A : Set n}  {tree left right : bt (Color ∧ A)} → {key : ℕ} → {value : A} → {c : Color}
   → tree ≡ node key ⟪ c , value ⟫ left right
   → c ≡ Red
   → RBtreeInvariant tree
   → (black-depth tree ≡ black-depth left ) ∧ (black-depth tree ≡ black-depth right)
red-children-eq {n} {A} {_} {left} {right} {key} {value} {c} () ceq rb-leaf
red-children-eq {n} {A} {(node key₁ ⟪ Red , value₁ ⟫ left₁ right₁)} {left} {right} {key} {value} {c} teq ceq (rb-red key₁ value₁ x x₁ x₂ rb rb₁)
    = ⟪ begin
          black-depth left₁ ⊔ black-depth right₁ ≡⟨ cong (λ k →   black-depth left₁ ⊔ k) (sym x₂)  ⟩
          black-depth left₁ ⊔ black-depth left₁ ≡⟨ ⊔-idem _  ⟩
          black-depth left₁ ≡⟨ cong black-depth (just-injective (cong node-left teq )) ⟩
          black-depth left ∎
    , begin
          black-depth left₁ ⊔ black-depth right₁ ≡⟨ cong (λ k →   k ⊔ black-depth right₁) x₂  ⟩
          black-depth right₁ ⊔ black-depth right₁ ≡⟨ ⊔-idem _  ⟩
          black-depth right₁ ≡⟨ cong black-depth (just-injective (cong node-right teq )) ⟩
          black-depth right ∎ ⟫
       where open ≡-Reasoning
red-children-eq {n} {A} {node key₁ ⟪ Black , value₁ ⟫ left₁ right₁} {left} {right} {key} {value} {c} teq ceq (rb-black key₁ value₁ x rb rb₁)
    = ⊥-elim ( ⊥-color (trans (cong color teq) ceq))

black-children-eq : {n : Level} {A : Set n}  {tree left right : bt (Color ∧ A)} → {key : ℕ} → {value : A} → {c : Color}
   → tree ≡ node key ⟪ c , value ⟫ left right
   → c ≡ Black
   → RBtreeInvariant tree
   → (black-depth tree ≡ suc (black-depth left) ) ∧ (black-depth tree ≡ suc (black-depth right))
black-children-eq {n} {A} {_} {left} {right} {key} {value} {c} () ceq rb-leaf
black-children-eq {n} {A} {.(node key₁ ⟪ Red , value₁ ⟫ _ _)} {left} {right} {key} {value} {c} teq ceq (rb-red key₁ value₁ x x₁ x₂ rb rb₁)
    = ⊥-elim ( ⊥-color (sym (trans (cong color teq) ceq)))
black-children-eq {n} {A} {(node key₁ ⟪ Black , value₁ ⟫ left₁ right₁)} {left} {right} {key} {value} {c} teq ceq rb2@(rb-black key₁ value₁ x rb rb₁) =
  ⟪ ( begin
        suc (black-depth left₁ ⊔ black-depth right₁) ≡⟨ cong (λ k → suc (black-depth left₁ ⊔ k)) (sym (RBtreeEQ rb2)) ⟩
        suc (black-depth left₁ ⊔ black-depth left₁) ≡⟨ cong (λ k → suc (black-depth k ⊔ black-depth k)) (just-injective (cong node-left teq )) ⟩
        suc (black-depth left ⊔ black-depth left) ≡⟨ ⊔-idem _ ⟩
        suc (black-depth left) ∎  ) ,  (
     begin
        suc (black-depth left₁ ⊔ black-depth right₁) ≡⟨ cong (λ k → suc (k ⊔ black-depth right₁)) (RBtreeEQ rb2) ⟩
        suc (black-depth right₁ ⊔ black-depth right₁) ≡⟨ cong (λ k → suc (black-depth k ⊔ black-depth k)) (just-injective (cong node-right teq )) ⟩
        suc (black-depth right ⊔ black-depth right) ≡⟨ ⊔-idem _ ⟩
        suc (black-depth right) ∎ ) ⟫ where open ≡-Reasoning

black-depth-cong  : {n : Level} (A : Set n)  {tree tree₁ : bt (Color ∧ A)}
   → tree ≡ tree₁ → black-depth tree ≡ black-depth tree₁
black-depth-cong {n} A {leaf} {leaf} eq = refl
black-depth-cong {n} A {leaf} {node _ _ _ _} ()
black-depth-cong {n} A {node key value tree tree₂} {leaf} ()
black-depth-cong {n} A {node key ⟪ Red , v0 ⟫ tree tree₂} {node key₁ ⟪ Red , v1 ⟫ tree₁ tree₃} eq
    = cong₂ _⊔_ (black-depth-cong A (just-injective (cong node-left eq ))) (black-depth-cong A (just-injective (cong node-right eq )))
black-depth-cong {n} A {node key ⟪ Red , v0 ⟫ tree tree₂} {node key₁ ⟪ Black , v1 ⟫ tree₁ tree₃} ()
black-depth-cong {n} A {node key ⟪ Black , v0 ⟫ tree tree₂} {node key₁ ⟪ Red , v1 ⟫ tree₁ tree₃} ()
black-depth-cong {n} A {node key ⟪ Black , v0 ⟫ tree tree₂} {node key₁ ⟪ Black , v1 ⟫ tree₁ tree₃} eq
    = cong₂ (λ j k → suc j ⊔ suc k) (black-depth-cong A (just-injective (cong node-left eq ))) (black-depth-cong A (just-injective (cong node-right eq )))


black-depth-resp  : {n : Level} (A : Set n)   (tree tree₁ : bt (Color ∧ A)) → {c1 c2 : Color}  { l1 l2 r1 r2 : bt (Color ∧ A)} {key1 key2 : ℕ} {value1 value2 : A}
   → tree ≡ node key1 ⟪ c1 , value1 ⟫ l1 r1 → tree₁ ≡ node key2 ⟪ c2 , value2 ⟫ l2 r2
   → color tree  ≡ color tree₁
   → black-depth l1 ≡ black-depth l2 → black-depth r1 ≡ black-depth r2
   → black-depth tree ≡ black-depth tree₁
black-depth-resp A leaf tree₁ {c1} {c2} {l1} {l2} {r1} {r2} {key1} {key2} {value1} {value2} () eq₁ ceq bd1 bd2
black-depth-resp A (node key value tree tree₂) leaf eq () ceq bd1 bd2
black-depth-resp A (node key ⟪ Red , value ⟫ tree tree₂) (node key₁ ⟪ Red , value₁ ⟫ tree₁ tree₃) {c1} {c2} {l1} {l2} {r1} {r2} eq eq₁ ceq bd1 bd2 = begin
    black-depth tree ⊔ black-depth tree₂ ≡⟨ cong₂ (λ j k → black-depth j ⊔ black-depth k) (just-injective (cong node-left eq )) (just-injective (cong node-right eq )) ⟩
    black-depth l1 ⊔ black-depth r1 ≡⟨ cong₂ _⊔_ bd1 bd2 ⟩
    black-depth l2 ⊔ black-depth r2 ≡⟨ cong₂ (λ j k → black-depth j ⊔ black-depth k) (just-injective (cong node-left (sym eq₁) )) (just-injective (cong node-right (sym eq₁) )) ⟩
    black-depth tree₁ ⊔ black-depth tree₃
    ∎ where open ≡-Reasoning
black-depth-resp A (node key ⟪ Red , value ⟫ tree tree₂) (node key₁ ⟪ Black , value₁ ⟫ tree₁ tree₃) eq eq₁ ceq bd1 bd2 = ⊥-elim ( ⊥-color (sym ceq ))
black-depth-resp A (node key ⟪ Black , value ⟫ tree tree₂) (node key₁ ⟪ Red , proj4 ⟫ tree₁ tree₃) eq eq₁ ceq bd1 bd2 = ⊥-elim ( ⊥-color ceq)
black-depth-resp A (node key ⟪ Black , value ⟫ tree tree₂) (node key₁ ⟪ Black , proj4 ⟫ tree₁ tree₃) {c1} {c2} {l1} {l2} {r1} {r2} eq eq₁ ceq bd1 bd2 = begin
    suc (black-depth tree ⊔ black-depth tree₂) ≡⟨ cong₂ (λ j k → suc (black-depth j ⊔ black-depth k)) (just-injective (cong node-left eq )) (just-injective (cong node-right eq )) ⟩
    suc (black-depth l1 ⊔ black-depth r1) ≡⟨ cong suc ( cong₂ _⊔_ bd1 bd2) ⟩
    suc (black-depth l2 ⊔ black-depth r2) ≡⟨ cong₂ (λ j k → suc (black-depth j ⊔ black-depth k)) (just-injective (cong node-left (sym eq₁) )) (just-injective (cong node-right (sym eq₁) )) ⟩
    suc (black-depth tree₁ ⊔ black-depth tree₃) ∎ where open ≡-Reasoning

red-children-eq1 : {n : Level} {A : Set n}  {tree left right : bt (Color ∧ A)} → {key : ℕ} → {value : A} → {c : Color}
   → tree ≡ node key ⟪ c , value ⟫ left right
   → color tree ≡ Red
   → RBtreeInvariant tree
   → (black-depth tree ≡ black-depth left ) ∧ (black-depth tree ≡ black-depth right)
red-children-eq1 {n} {A} {tree} {left} {right} {key} {value} {c} eq ceq rb = red-children-eq eq ((trans  (sym (cong color eq)  ) ceq )) rb

black-children-eq1 : {n : Level} {A : Set n}  {tree left right : bt (Color ∧ A)} → {key : ℕ} → {value : A} → {c : Color}
   → tree ≡ node key ⟪ c , value ⟫ left right
   → color tree ≡ Black
   → RBtreeInvariant tree
   → (black-depth tree ≡ suc (black-depth left) ) ∧ (black-depth tree ≡ suc (black-depth right))
black-children-eq1 {n} {A} {tree} {left} {right} {key} {value} {c} eq ceq rb = black-children-eq eq ((trans  (sym (cong color eq)  ) ceq )) rb


rbi-from-red-black : {n : Level } {A : Set n} → (n1 rp-left : bt (Color ∧ A)) → (kp : ℕ) → (vp : Color ∧ A)
    → RBtreeInvariant n1 → RBtreeInvariant rp-left
    → black-depth n1 ≡ black-depth rp-left
    → color n1 ≡ Black → color rp-left ≡ Black →  ⟪ Red , proj2 vp ⟫ ≡ vp
    → RBtreeInvariant (node kp vp n1 rp-left)
rbi-from-red-black leaf leaf kp vp rb1 rbp deq ceq1 ceq2 ceq3
    = subst (λ k → RBtreeInvariant (node kp k leaf leaf)) ceq3 (rb-red kp (proj2 vp)  refl refl refl rb-leaf rb-leaf)
rbi-from-red-black leaf (node key ⟪ .Black , proj3 ⟫ trpl trpl₁) kp vp rb1 rbp deq ceq1 refl ceq3
    = subst (λ k → RBtreeInvariant (node kp k _ _)) ceq3 (rb-red kp (proj2 vp) refl refl deq rb1 rbp)
rbi-from-red-black (node key ⟪ .Black , proj3 ⟫ tn1 tn2) leaf kp vp rb1 rbp deq refl ceq2 ceq3
    = subst (λ k → RBtreeInvariant (node kp k _ _)) ceq3 (rb-red kp (proj2 vp) refl refl deq rb1 rbp)
rbi-from-red-black (node key ⟪ .Black , proj3 ⟫ tn1 tn2) (node key₁ ⟪ .Black , proj4 ⟫ trpl trpl₁) kp vp rb1 rbp deq refl refl ceq3
  = subst (λ k → RBtreeInvariant (node kp k _ _)) ceq3 (rb-red kp (proj2 vp) refl refl deq rb1 rbp )

⊔-succ : {m n : ℕ} → suc (m ⊔ n) ≡ suc m ⊔ suc n
⊔-succ {m} {n} = refl

RB-repl-node  : {n : Level} {A : Set n}  → (tree repl : bt (Color ∧ A)) → {key : ℕ} → {value : A}
     → replacedRBTree key value tree repl → ¬ ( repl ≡ leaf)
RB-repl-node {n} {A} .leaf .(node _ ⟪ Red , _ ⟫ leaf leaf) rbr-leaf ()
RB-repl-node {n} {A} .(node _ ⟪ _ , _ ⟫ _ _) .(node _ ⟪ _ , _ ⟫ _ _) rbr-node ()
RB-repl-node {n} {A} .(node _ ⟪ _ , _ ⟫ _ _) .(node _ ⟪ _ , _ ⟫ _ _) (rbr-right x x₁ rpl) ()
RB-repl-node {n} {A} .(node _ ⟪ _ , _ ⟫ _ _) .(node _ ⟪ _ , _ ⟫ _ _) (rbr-left x x₁ rpl) ()
RB-repl-node {n} {A} .(node _ ⟪ Black , _ ⟫ _ _) .(node _ ⟪ Black , _ ⟫ _ _) (rbr-black-right x x₁ rpl) ()
RB-repl-node {n} {A} .(node _ ⟪ Black , _ ⟫ _ _) .(node _ ⟪ Black , _ ⟫ _ _) (rbr-black-left x x₁ rpl) ()
RB-repl-node {n} {A} .(node _ ⟪ Black , _ ⟫ (node _ ⟪ Red , _ ⟫ _ _) _) .(node _ ⟪ Red , _ ⟫ (node _ ⟪ Black , _ ⟫ _ _) (to-black _)) (rbr-flip-ll x x₁ x₂ x₃) ()
RB-repl-node {n} {A} .(node _ ⟪ Black , _ ⟫ (node _ ⟪ Red , _ ⟫ _ _) _) .(node _ ⟪ Red , _ ⟫ (node _ ⟪ Black , _ ⟫ _ _) (to-black _)) (rbr-flip-lr x x₁ x₂ x₃ x₄) ()
RB-repl-node {n} {A} .(node _ ⟪ Black , _ ⟫ _ (node _ ⟪ Red , _ ⟫ _ _)) .(node _ ⟪ Red , _ ⟫ (to-black _) (node _ ⟪ Black , _ ⟫ _ _)) (rbr-flip-rl x x₁ x₂ x₃ x₄) ()
RB-repl-node {n} {A} .(node _ ⟪ Black , _ ⟫ _ (node _ ⟪ Red , _ ⟫ _ _)) .(node _ ⟪ Red , _ ⟫ (to-black _) (node _ ⟪ Black , _ ⟫ _ _)) (rbr-flip-rr x₁ x₂ x₃ x₄) ()
RB-repl-node {n} {A} .(node _ ⟪ Black , _ ⟫ (node _ ⟪ Red , _ ⟫ _ _) _) .(node _ ⟪ Black , _ ⟫ _ (node _ ⟪ Red , _ ⟫ _ _)) (rbr-rotate-ll x x₁ x₂) ()
RB-repl-node {n} {A} .(node x₂ ⟪ Black , _ ⟫ (node x₃ ⟪ Red , _ ⟫ _ _) _) .(node x₄ ⟪ Black , _ ⟫ (node x₃ ⟪ Red , _ ⟫ _ x) (node x₂ ⟪ Red , _ ⟫ x₁ _)) (rbr-rotate-lr x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) ()
RB-repl-node {n} {A} .(node x₂ ⟪ Black , _ ⟫ _ (node x₃ ⟪ Red , _ ⟫ _ _)) .(node x₄ ⟪ Black , _ ⟫ (node x₂ ⟪ Red , _ ⟫ _ x) (node x₃ ⟪ Red , _ ⟫ x₁ _)) (rbr-rotate-rl x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) ()
RB-repl-node {n} {A} .(node _ ⟪ Black , _ ⟫ _ (node _ ⟪ Red , _ ⟫ _ _)) .(node _ ⟪ Black , _ ⟫ (node _ ⟪ Red , _ ⟫ _ _) _) (rbr-rotate-rr x x₁ x₂) ()

RBTPred : {n : Level}  (A : Set n) (m : Level) → Set (n Level.⊔ Level.suc m)
RBTPred {n} A m = (key : ℕ) → (value : A) → (before after : bt (Color ∧ A)) → replacedRBTree key value before after → Set m

RBTI-induction : {n m : Level} (A : Set n) → (tree tree1 repl : bt (Color ∧ A)) → (key : ℕ) → (value : A) → tree ≡ tree1 → (rbt : replacedRBTree key value tree repl  )
    → {P : RBTPred A m } 
    → ( P key value leaf (node key ⟪ Red , value ⟫ leaf leaf) rbr-leaf  
      ∧  ( (ca : Color ) → (value₂ : A) → (t t₁ : bt (Color ∧ A)) → P key value (node key ⟪ ca , value₂ ⟫ t t₁) (node key ⟪ ca , value ⟫ t t₁) rbr-node )
      ∧  ( {k : ℕ } {v1 : A} → {ca : Color} → {t t1 t2 : bt (Color ∧ A)} → (x : color t2 ≡ color t) ( x₁ : k < key ) → (rbt : replacedRBTree key value t2 t )
         → P key value t2 t rbt → P key value (node k ⟪ ca , v1 ⟫ t1 t2) (node k ⟪ ca , v1 ⟫ t1 t) (rbr-right x x₁ rbt ) )
      ∧  ( {k : ℕ } {v1 : A} → {ca : Color} → {t t1 t2 : bt (Color ∧ A)} → (x : color t1 ≡ color t) ( x₁ : key < k ) → (rbt : replacedRBTree key value t1 t )
         → P key value t1 t rbt 
         → P key value (node k ⟪ ca , v1 ⟫ t1 t2) (node k ⟪ ca , v1 ⟫ t t2) (rbr-left x x₁ rbt))
      ∧ ( {t t₁ t₂ : bt (Color ∧ A)} {value₁ : A} {key₁ : ℕ} → (x : color t₂ ≡ Red) → (x₁ : key₁ < key)  → (rbt : replacedRBTree key value t₁ t₂ ) 
         → P key value t₁ t₂ rbt 
         → P key value (node key₁ ⟪ Black , value₁ ⟫ t t₁) (node key₁ ⟪ Black , value₁ ⟫ t t₂) (rbr-black-right x x₁ rbt)  )
      ∧  ({t t₁ t₂ : bt (Color ∧ A)} {value₁ : A} {key₁ : ℕ} → (x : color t₂ ≡ Red ) → (x₁ : key < key₁ ) → (rbt : replacedRBTree key value t₁ t₂ )
         → P key value t₁ t₂ rbt 
         → P key value (node key₁ ⟪ Black , value₁ ⟫ t₁ t) (node key₁ ⟪ Black , value₁ ⟫ t₂ t) (rbr-black-left x x₁ rbt)  ) 
      ∧ (  {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A}
         → (x : color t₂ ≡ Red ) → (x₁ : color uncle ≡ Red ) → (x₂ : key < kp ) → (rbt : replacedRBTree key value t₁ t₂ )
         →  P key value t₁ t₂ rbt
         →  P key value (node kg ⟪ Black , vg ⟫ (node kp ⟪ Red , vp ⟫ t₁ t) uncle) (node kg ⟪ Red , vg ⟫ (node kp ⟪ Black , vp ⟫ t₂ t) (to-black uncle)) 
            (rbr-flip-ll x x₁ x₂ rbt))
      ∧ ( {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A} → (x : color t₂ ≡ Red ) → (x₁ : color uncle ≡ Red ) →  (x₂ : kp < key ) → (x₃ : key < kg)   
         → (rbt : replacedRBTree key value t₁ t₂ )
         →  P key value t₁ t₂ rbt
         →  P key value (node kg ⟪ Black , vg ⟫ (node kp ⟪ Red , vp ⟫ t t₁) uncle) (node kg ⟪ Red , vg ⟫ (node kp ⟪ Black , vp ⟫ t t₂) (to-black uncle)) 
           (rbr-flip-lr x x₁ x₂ x₃ rbt) )
      ∧ ( {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A}
         → (x : color t₂ ≡ Red ) → (x₁ : color uncle ≡ Red ) → (x₂ : kg < key ) → (x₃ : key < kp)  → (rbt : replacedRBTree key value t₁ t₂  )
         → P key value t₁ t₂ rbt
         → P key value (node kg ⟪ Black , vg ⟫ uncle (node kp ⟪ Red , vp ⟫ t₁ t))
            (node kg ⟪ Red , vg ⟫ (to-black uncle) (node kp ⟪ Black , vp ⟫ t₂ t))
            (rbr-flip-rl x x₁ x₂ x₃ rbt)) 
      ∧ ( {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A}
         → (x : color t₂ ≡ Red ) → (x₁ : color uncle ≡ Red ) → (x₂ : kp < key )  → (rbt : replacedRBTree key value t₁ t₂  )
         → P key value t₁ t₂ rbt
         → P key value (node kg ⟪ Black , vg ⟫ uncle (node kp ⟪ Red , vp ⟫ t t₁)) (node kg ⟪ Red , vg ⟫ (to-black uncle) (node kp ⟪ Black , vp ⟫ t t₂))
            (rbr-flip-rr x x₁ x₂ rbt)  ) 
      ∧ ( {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A} → (x : color t₂ ≡ Red) → (x₁ : key < kp ) → (rbt : replacedRBTree key value t₁ t₂  )
         → P key value t₁ t₂ rbt
         → P key value (node kg ⟪ Black , vg ⟫ (node kp ⟪ Red , vp ⟫ t₁ t) uncle) (node kp ⟪ Black , vp ⟫ t₂ (node kg ⟪ Red , vg ⟫ t uncle)) (rbr-rotate-ll x x₁ rbt))
      ∧ ({t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A}
         → (x : color t₂ ≡ Red ) → (x₁ : kp < key ) → (rbt : replacedRBTree key value t₁ t₂ )
         → P key value t₁ t₂ rbt
         →  P key value (node kg ⟪ Black , vg ⟫ uncle (node kp ⟪ Red , vp ⟫ t t₁)) (node kp ⟪ Black , vp ⟫ (node kg ⟪ Red , vg ⟫ uncle t) t₂)
            (rbr-rotate-rr x x₁ rbt)  ) 
      ∧ ({t t₁ uncle : bt (Color ∧ A)} (t₂ t₃ : bt (Color ∧ A)) (kg kp kn : ℕ) {vg vp vn : A}
         → (x : color t₃ ≡ Black) → (x₁ : kp < key )→ (x₂ : key < kg )
         → (rbt : replacedRBTree key value t₁ (node kn ⟪ Red , vn ⟫ t₂ t₃))
         → P key value t₁ (node kn ⟪ Red , vn ⟫ t₂ t₃) rbt
         → P key value (node kg ⟪ Black , vg ⟫ (node kp ⟪ Red , vp ⟫ t t₁) uncle) (node kn ⟪ Black , vn ⟫ (node kp ⟪ Red , vp ⟫ t t₂) (node kg ⟪ Red , vg ⟫ t₃ uncle))
            (rbr-rotate-lr t₂ t₃ kg kp kn x x₁ x₂ rbt)  ) 
      ∧ ( {t t₁ uncle : bt (Color ∧ A)} (t₂ t₃ : bt (Color ∧ A)) (kg kp kn : ℕ) {vg vp vn : A}
         → (x : color t₃ ≡ Black) → (x₁ : kg < key) → (x₂ : key < kp )
         → (rbt : replacedRBTree key value t₁ (node kn ⟪ Red , vn ⟫ t₂ t₃) )
         → P key value t₁ (node kn ⟪ Red , vn ⟫ t₂ t₃) rbt
         → P key value (node kg ⟪ Black , vg ⟫ uncle (node kp ⟪ Red , vp ⟫ t₁ t)) (node kn ⟪ Black , vn ⟫ (node kg ⟪ Red , vg ⟫ uncle t₂) (node kp ⟪ Red , vp ⟫ t₃ t))
            (rbr-rotate-rl t₂ t₃ kg kp kn x x₁ x₂ rbt)  )) 
    → P key value tree repl rbt
RBTI-induction {n} {m} A tree leaf repl key value eq rbr-leaf {P} p = proj1 p
RBTI-induction {n} {m} A tree (node key₁ value₁ tree1 tree2) repl key value eq (rbr-node {value₂} {ca} {t} {t1} ) {P} p = proj1 (proj2 p) ca value₂ t t1
RBTI-induction {n} {m} A tree (node key₁ value₁ tree1 tree2) repl key value eq (rbr-right {k} {v1} {ca} {t} {t1} {t2} x x₁ rbt) {P} p 
   = proj1 (proj2 (proj2 p)) x x₁ rbt (RBTI-induction A _ _ _ key value refl rbt {P} p)
RBTI-induction {n} {m} A tree (node key₁ value₁ tree1 tree2) repl key value eq (rbr-left x x₁ rbt) {P} p 
   = proj1 (proj2 (proj2 (proj2 p))) x x₁ rbt (RBTI-induction A _ _ _ key value refl rbt {P} p)
RBTI-induction {n} {m} A tree (node key₁ value₁ tree1 tree2) repl key value eq (rbr-black-right x x₁ rbt) {P} p 
   = proj1 (proj2 (proj2 (proj2 (proj2 p)))) x x₁ rbt (RBTI-induction A _ _ _ key value refl rbt {P} p)
RBTI-induction {n} {m} A tree (node key₁ value₁ tree1 tree2) repl key value eq (rbr-black-left x x₁ rbt) {P} p 
   = proj1 (proj2 (proj2 (proj2 (proj2 (proj2 p))))) x x₁ rbt (RBTI-induction A _ _ _ key value refl rbt {P} p)
RBTI-induction {n} {m} A tree (node key₁ value₁ tree1 tree2) repl key value eq (rbr-flip-ll {t} {t₁} {t₂} x x₁ x₂ rbt) {P} p 
   = proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 p)))))) x x₁ x₂ rbt (RBTI-induction A _ _ _ key value refl rbt {P} p) 
RBTI-induction {n} {m} A tree (node key₁ value₁ tree1 tree2) repl key value eq (rbr-flip-lr x x₁ x₂ x₃ rbt) {P} p 
   = proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 p))))))) x x₁ x₂ x₃ rbt (RBTI-induction A _ _ _ key value refl rbt {P} p)
RBTI-induction {n} {m} A tree (node key₁ value₁ tree1 tree2) repl key value eq (rbr-flip-rl x x₁ x₂ x₃ rbt) {P} p 
   = proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 p)))))))) x x₁ x₂ x₃ rbt (RBTI-induction A _ _ _ key value refl rbt {P} p)
RBTI-induction {n} {m} A tree (node key₁ value₁ tree1 tree2) repl key value eq (rbr-flip-rr x x₁ x₂ rbt) {P} p 
   = proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 p))))))))) x x₁ x₂ rbt (RBTI-induction A _ _ _ key value refl rbt {P} p)
RBTI-induction {n} {m} A tree (node key₁ value₁ tree1 tree2) repl key value eq (rbr-rotate-ll x x₁ rbt) {P} p 
   = proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 p)))))))))) x x₁ rbt (RBTI-induction A _ _ _ key value refl rbt {P} p)
RBTI-induction {n} {m} A tree (node key₁ value₁ tree1 tree2) repl key value eq (rbr-rotate-rr x x₁ rbt) {P} p 
   = proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 p))))))))))) x x₁ rbt (RBTI-induction A _ _ _ key value refl rbt {P} p)
RBTI-induction {n} {m} A tree (node key₁ value₁ tree1 tree2) repl key value eq (rbr-rotate-lr t₂ t₃ kg kp kn x x₁ x₂ rbt) {P} p 
   = proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 p)))))))))))) _ _ _ _ _ x x₁ x₂ rbt (RBTI-induction A _ _ _ key value refl rbt {P} p)
RBTI-induction {n} {m} A tree (node key₁ value₁ tree1 tree2) repl key value eq (rbr-rotate-rl t₂ t₃ kg kp kn x x₁ x₂ rbt) {P} p 
   = proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 p)))))))))))) _ _ _ _ _ x x₁ x₂ rbt (RBTI-induction A _ _ _ key value refl rbt {P} p)


RB-repl→eq  : {n : Level} {A : Set n}  → (tree repl : bt (Color ∧ A)) → {key : ℕ} → {value : A}
     → RBtreeInvariant tree
     → replacedRBTree key value tree repl → black-depth tree ≡ black-depth repl
RB-repl→eq {n} {A} tree repl {key} {value} rbt rbr = RBTI-induction A tree tree repl key value refl rbr  {λ key value b a rbt → black-depth b ≡ black-depth a } 
     ⟪ refl , ⟪ (λ ca _ _ _ → lem00 ca _ _ _ ) , ⟪ 
         (λ {k} {v1} {ca} {t} {t1} {t2} → lem01 {k} {v1} {ca} {t} {t1} {t2}) , ⟪ (λ {k} {v1} {ca} {t} {t1} {t2} → lem02 {k} {v1} {ca} {t} {t1} {t2}) , ⟪ 
         (λ {t} {t₁} {t₂} {v1} → lem03 {t} {t₁} {t₂} {v1} ) , ⟪ (λ {t} {t₁} {t₂} {v₁} {k₁} → lem04 {t} {t₁} {t₂} {v₁} {k₁})  , ⟪ 
         (λ {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} → lem05 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp}) , ⟪ 
         (λ {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} → lem06 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp}) , ⟪ 
         (λ {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} → lem07 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp}) , ⟪ 
         (λ {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} → lem08 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp}) , ⟪ 
         (λ {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} → lem09 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp}) , ⟪ 
         (λ {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} → lem10 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp}) , ⟪ 
         (λ {t} {t₁} {uncle} t₂ t₃ kg kp kn {vg} {vp} {vn} → lem11 {t} {t₁} {uncle} t₂ t₃ kg kp kn {vg} {vp} {vn} ) , 
         (λ {t} {t₁} {uncle} t₂ t₃ kg kp kn {vg} {vp} {vn} → lem12 {t} {t₁} {uncle} t₂ t₃ kg kp kn {vg} {vp} {vn} ) ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ where
      lem00 : (ca : Color) → ( value₂ : A) → (t t₁ : bt (Color ∧ A)) → black-depth (node key ⟪ ca , value₂ ⟫ t t₁) ≡ black-depth (node key ⟪ ca , value ⟫ t t₁)
      lem00 Black v t t₁ = refl
      lem00 Red v t t₁ = refl
      lem01 : {k : ℕ} {v1 : A} {ca : Color} {t t1 t2 : bt (Color ∧ A)} (x : color t2 ≡ color t) (x₁ : k < key)
            (rbt : replacedRBTree key value t2 t) → black-depth t2 ≡ black-depth t → black-depth (node k ⟪ ca , v1 ⟫ t1 t2) ≡ black-depth (node k ⟪ ca , v1 ⟫ t1 t)
      lem01 {k} {v1} {Red} {t} {t1} {t2} ceq x₁ rbt prev = cong ( λ k → black-depth t1 ⊔ k ) prev 
      lem01 {k} {v1} {Black} {t} {t1} {t2} ceq x₁ rbt prev = cong ( λ k → suc (black-depth t1 ⊔ k) ) prev 
      lem02 :  {k : ℕ} {v1 : A} {ca : Color} {t t1 t2 : bt (Color ∧ A)} (x : color t1 ≡ color t) (x₁ : key < k)
            (rbt₁ : replacedRBTree key value t1 t) → black-depth t1 ≡ black-depth t → black-depth (node k ⟪ ca , v1 ⟫ t1 t2) ≡ black-depth (node k ⟪ ca , v1 ⟫ t t2)
      lem02 {k} {v1} {Red} {t} {t1} {t2} ceq x₁ rbt prev = cong ( λ k → k ⊔ _ ) prev
      lem02 {k} {v1} {Black} {t} {t1} {t2} ceq x₁ rbt prev = cong ( λ k → suc (k ⊔ _) ) prev
      lem03 :  {t t₁ t₂ : bt (Color ∧ A)} {value₁ : A} {key₁ : ℕ} (x : color t₂ ≡ Red) (x₁ : key₁ < key) (rbt₁ : replacedRBTree key value t₁ t₂) →
            black-depth t₁ ≡ black-depth t₂ → suc (black-depth t ⊔ black-depth t₁) ≡ suc (black-depth t ⊔ black-depth t₂) 
      lem03 {t} x x₁ rbt eq = cong (λ k → suc (black-depth t ⊔ k)) eq
      lem04 : {t t₁ t₂ : bt (Color ∧ A)} {value₁ : A} {key₁ : ℕ} (x : color t₂ ≡ Red) (x₁ : key < key₁) (rbt₁ : replacedRBTree key value t₁ t₂) →
            black-depth t₁ ≡ black-depth t₂ → suc (black-depth t₁ ⊔ black-depth t) ≡ suc (black-depth t₂ ⊔ black-depth t)
      lem04 {t} {t₁} {t₂} {v₁} x x₁ rbt eq = cong (λ k → suc (k ⊔ black-depth t)) eq
      lem05 :  {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A} (x : color t₂ ≡ Red) (x₁ : color uncle ≡ Red) (x₂ : key < kp) (rbt₁ : replacedRBTree key value t₁ t₂) →
            black-depth t₁ ≡ black-depth t₂ → suc (black-depth t₁ ⊔ black-depth t ⊔ black-depth uncle) ≡ suc (black-depth t₂ ⊔ black-depth t) ⊔ black-depth (to-black uncle)
      lem05 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} x x₁ x₂ rbt eq = begin
          suc (black-depth t₁ ⊔ black-depth t ⊔ black-depth uncle) ≡⟨ cong (λ k → suc (k ⊔ _ ⊔ _ )) eq ⟩
          suc (black-depth t₂ ⊔ black-depth t) ⊔ suc (black-depth uncle)  ≡⟨ cong (λ k →  suc (black-depth t₂ ⊔ black-depth t) ⊔ k) (to-black-eq uncle x₁ ) ⟩
          suc (black-depth t₂ ⊔ black-depth t) ⊔ black-depth (to-black uncle)  ∎ where open ≡-Reasoning
      lem06 : {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A} (x : color t₂ ≡ Red) (x₁ : color uncle ≡ Red) (x₂ : kp < key)
            (x₃ : key < kg) (rbt₁ : replacedRBTree key value t₁ t₂) →
            black-depth t₁ ≡ black-depth t₂ → suc (black-depth t ⊔ black-depth t₁ ⊔ black-depth uncle) ≡ suc (black-depth t ⊔ black-depth t₂) ⊔ black-depth (to-black uncle)
      lem06 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} x x₁ x₂ x₃ rbt eq = begin
          suc (black-depth t ⊔ black-depth t₁ ⊔ black-depth uncle) ≡⟨ cong (λ k → suc (black-depth t ⊔ k ⊔ _ )) eq ⟩
          suc (black-depth t ⊔ black-depth t₂) ⊔ suc (black-depth uncle)  ≡⟨ cong (λ k →  suc (black-depth t ⊔ black-depth t₂) ⊔ k) (to-black-eq uncle x₁ ) ⟩
          suc (black-depth t ⊔ black-depth t₂) ⊔ black-depth (to-black uncle)  ∎ where open ≡-Reasoning
      lem07 : {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A} (x : color t₂ ≡ Red) (x₁ : color uncle ≡ Red) (x₂ : kg < key)
            (x₃ : key < kp) (rbt₁ : replacedRBTree key value t₁ t₂) →
            black-depth t₁ ≡ black-depth t₂ → suc (black-depth uncle ⊔ (black-depth t₁ ⊔ black-depth t)) ≡ black-depth (to-black uncle) ⊔ suc (black-depth t₂ ⊔ black-depth t)
      lem07 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} x x₁ x₂ x₃ rbt eq = begin
          suc (black-depth uncle ⊔ (black-depth t₁ ⊔ black-depth t)) ≡⟨ cong (λ k → suc (black-depth uncle ⊔ (k ⊔  _))) eq ⟩
          suc (black-depth uncle ⊔ (black-depth t₂ ⊔ black-depth t)) ≡⟨ cong (λ k → k ⊔ _) (to-black-eq uncle x₁) ⟩
          black-depth (to-black uncle) ⊔ suc (black-depth t₂ ⊔ black-depth t)  ∎ where open ≡-Reasoning
      lem08 : {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A} (x : color t₂ ≡ Red) (x₁ : color uncle ≡ Red) (x₂ : kp < key) (rbt₁ : replacedRBTree key value t₁ t₂) →
            black-depth t₁ ≡ black-depth t₂ → suc (black-depth uncle ⊔ (black-depth t ⊔ black-depth t₁)) ≡ black-depth (to-black uncle) ⊔ suc (black-depth t ⊔ black-depth t₂)
      lem08 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} x x₁ x₂ rbt eq = begin
          suc (black-depth uncle ⊔ (black-depth t ⊔ black-depth t₁)) ≡⟨ cong (λ k → suc (black-depth uncle ⊔ (_ ⊔  k))) eq ⟩
          suc (black-depth uncle ⊔ (black-depth t ⊔ black-depth t₂)) ≡⟨ cong (λ k → k ⊔ _) (to-black-eq uncle x₁) ⟩
          black-depth (to-black uncle) ⊔ suc (black-depth t ⊔ black-depth t₂)  ∎ where open ≡-Reasoning
      lem09 :  {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A} (x : color t₂ ≡ Red) (x₁ : key < kp) (rbt₁ : replacedRBTree key value t₁ t₂) →
            black-depth t₁ ≡ black-depth t₂ → suc (black-depth t₁ ⊔ black-depth t ⊔ black-depth uncle) ≡ suc (black-depth t₂ ⊔ (black-depth t ⊔ black-depth uncle))
      lem09 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} x x₁ rbt eq = begin
          suc (black-depth t₁ ⊔ black-depth t ⊔ black-depth uncle) ≡⟨ cong (λ k → suc (k ⊔ _ ⊔ _)) eq ⟩
          suc (black-depth t₂ ⊔ black-depth t ⊔ black-depth uncle)  ≡⟨ ⊔-assoc (suc (black-depth t₂))  (suc (black-depth t)) (suc (black-depth uncle)) ⟩
          suc (black-depth t₂ ⊔ (black-depth t ⊔ black-depth uncle))   ∎ where open ≡-Reasoning
      lem10 : {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A} (x : color t₂ ≡ Red) (x₁ : kp < key) (rbt₁ : replacedRBTree key value t₁ t₂) →
            black-depth t₁ ≡ black-depth t₂ → suc (black-depth uncle ⊔ (black-depth t ⊔ black-depth t₁)) ≡ suc (black-depth uncle ⊔ black-depth t ⊔ black-depth t₂)
      lem10 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} x x₁ rbt eq = begin
          suc (black-depth uncle ⊔ (black-depth t ⊔ black-depth t₁)) ≡⟨ cong (λ k → suc (black-depth uncle ⊔ (_ ⊔ k))) eq ⟩
          suc (black-depth uncle ⊔ (black-depth t ⊔ black-depth t₂))  ≡⟨ sym (⊔-assoc (suc (black-depth uncle))  (suc (black-depth t)) (suc (black-depth t₂))) ⟩
          suc (black-depth uncle ⊔ black-depth t ⊔ black-depth t₂)   ∎ where open ≡-Reasoning
      lem11 :  {t t₁ uncle : bt (Color ∧ A)} (t₂ t₃ : bt (Color ∧ A)) (kg kp kn : ℕ) {vg vp vn : A} (x : color t₃ ≡ Black) (x₁ : kp < key) (x₂ : key < kg)
            (rbt₁ : replacedRBTree key value t₁ (node kn ⟪ Red , vn ⟫ t₂ t₃)) →
            black-depth t₁ ≡ black-depth t₂ ⊔ black-depth t₃ → suc (black-depth t ⊔ black-depth t₁ ⊔ black-depth uncle) ≡ suc
            (black-depth t ⊔ black-depth t₂ ⊔ (black-depth t₃ ⊔ black-depth uncle))
      lem11 {t} {t₁} {uncle} t₂ t₃ kg kp kn {vg} {vp} {vn} x x₁ x₂ rbt eq = begin
          suc (black-depth t ⊔ black-depth t₁ ⊔ black-depth uncle) ≡⟨ cong (λ k → suc (black-depth t ⊔ k ⊔ _)) eq ⟩
          suc ((black-depth t ⊔ (black-depth t₂ ⊔ black-depth t₃ )) ⊔ black-depth uncle)  ≡⟨ cong (λ k → suc (k ⊔ black-depth uncle )) (sym ( ⊔-assoc (black-depth t) (black-depth t₂) _ )) ⟩
          suc (((black-depth t ⊔ black-depth t₂) ⊔ black-depth t₃) ⊔ black-depth uncle)   ≡⟨ cong suc ( ⊔-assoc _ (black-depth t₃) (black-depth uncle) ) ⟩
          suc ((black-depth t ⊔ black-depth t₂ ) ⊔ (black-depth t₃ ⊔ black-depth uncle))  ∎ where open ≡-Reasoning
      lem12 : {t t₁ uncle : bt (Color ∧ A)} (t₂ t₃ : bt (Color ∧ A)) (kg kp kn : ℕ) {vg vp vn : A} (x : color t₃ ≡ Black) (x₁ : kg < key) (x₂ : key < kp)
            (rbt₁ : replacedRBTree key value t₁ (node kn ⟪ Red , vn ⟫ t₂ t₃)) 
            → black-depth t₁ ≡ black-depth t₂ ⊔ black-depth t₃ 
            → suc (black-depth uncle ⊔ (black-depth t₁ ⊔ black-depth t)) ≡ suc (black-depth uncle ⊔ black-depth t₂ ⊔ (black-depth t₃ ⊔ black-depth t))
      lem12 {t} {t₁} {uncle} t₂ t₃ kg kp kn {vg} {vp} {vn} x x₁ x₂ rbt eq = begin
          suc (black-depth uncle ⊔ (black-depth t₁ ⊔ black-depth t)) ≡⟨ cong (λ k → suc (black-depth uncle ⊔ (k ⊔ _))) eq ⟩
          suc (black-depth uncle ⊔ ((black-depth t₂ ⊔ black-depth t₃) ⊔ black-depth t)) ≡⟨ cong (λ k → suc (black-depth uncle ⊔ k )) (( ⊔-assoc (black-depth t₂) (black-depth t₃) _ )) ⟩ 
          suc (black-depth uncle ⊔ (black-depth t₂ ⊔ (black-depth t₃ ⊔ black-depth t)))  ≡⟨ cong suc (sym (⊔-assoc (black-depth uncle) (black-depth t₂) (black-depth t₃ ⊔ black-depth t )))  ⟩
          suc (black-depth uncle ⊔ black-depth t₂ ⊔ (black-depth t₃ ⊔ black-depth t))  ∎ where open ≡-Reasoning


RB-repl→ti>  : {n : Level} {A : Set n}  → (tree repl : bt (Color ∧ A)) → (key key₁ : ℕ) → (value : A)
     → replacedRBTree key value tree repl → key₁ < key → tr> key₁ tree → tr> key₁ repl
RB-repl→ti>  {n} {A} tree repl key key₁ value rbr s1 s2 = RBTI-induction A tree tree repl key value refl rbr  
  {λ key value b a rbt → (key₁ : ℕ) → key₁ < key → tr> key₁ b  → tr> key₁ a}
     ⟪ (λ _ x _ → ⟪ x , ⟪ tt , tt ⟫ ⟫ ) , ⟪ lem00 , ⟪ (λ {k} {v1} {ca} {t} {t1} {t2} → lem01 {k} {v1} {ca} {t} {t1} {t2} ) , ⟪ 
        (λ {k} {v1} {ca} {t} {t1} {t2} → lem02 {k} {v1} {ca} {t} {t1} {t2} ) , ⟪ 
        (λ {t} {t₁} {t₂} {v1} x x₁ rbt prev k3 x₃ x₂ → lem03 {t} {t₁} {t₂} {v1} x x₁ rbt prev k3 x₃ x₂ ) , ⟪ 
        (λ {t} {t₁} {t₂} {v₁} {key₁} → lem04 {t} {t₁} {t₂} {v₁} {key₁}  ) , ⟪ 
        (λ {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} → lem05 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} )  , ⟪ 
        (λ {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} → lem06 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} )  , ⟪ 
        (λ {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} → lem07 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp}  ) , ⟪ 
        (λ {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} → lem08 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp}) , ⟪ 
        (λ {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} → lem09 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} ) , ⟪ 
        (λ {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} → lem11 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} ) , ⟪ 
        (λ {t} {t₁} {t₂} → lem12 {t} {t₁} {t₂} ) , (λ {t} {t₁} {t₂} → lem13 {t} {t₁} {t₂} ) ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ key₁ s1 s2 where
      lem00 :  (ca : Color) (value₂ : A) (t t₁ : bt (Color ∧ A)) (key₂ : ℕ) → key₂ < key → (key₂ < key) ∧ tr> key₂ t ∧ tr> key₂ t₁ → (key₂ < key) ∧ tr> key₂ t ∧ tr> key₂ t₁
      lem00 ca v2 t t₁ k2 x ⟪ x₁ , ⟪ x₂ , x₃ ⟫ ⟫ = ⟪ x , ⟪ x₂ , x₃  ⟫ ⟫
      lem01 :   {k : ℕ} {v1 : A} {ca : Color} {t t1 t2 : bt (Color ∧ A)} (x : color t2 ≡ color t) (x₁ : k < key)
            (rbt : replacedRBTree key value t2 t) → ((key₂ : ℕ) → key₂ < key → tr> key₂ t2 → tr> key₂ t) → (key₂ : ℕ) → key₂ < key →
            (key₂ < k) ∧ tr> key₂ t1 ∧ tr> key₂ t2 → (key₂ < k) ∧ tr> key₂ t1 ∧ tr> key₂ t
      lem01 {k} {v1} {ca} {t} {t1} {t2} ceq x₁ rbt prev k2 x x₂  = ⟪ proj1 x₂ , ⟪ proj1 (proj2 x₂) , prev _ x (proj2 (proj2 x₂)) ⟫ ⟫
      lem02 : {k : ℕ} {v1 : A} {ca : Color} {t t1 t2 : bt (Color ∧ A)} (x : color t1 ≡ color t) (x₁ : key < k) (rbt : replacedRBTree key value t1 t) →
            ((key₂ : ℕ) → key₂ < key → tr> key₂ t1 → tr> key₂ t) → (key₂ : ℕ) → key₂ < key → (key₂ < k) ∧ tr> key₂ t1 ∧ tr> key₂ t2 → (key₂ < k) ∧ tr> key₂ t ∧ tr> key₂ t2
      lem02 {k} {v1} {ca} {t} {t1} {t2} ceq x₁ rbt prev k2 x x₂ = ⟪ proj1 x₂ , ⟪ prev _ x (proj1 (proj2 x₂)) , proj2 (proj2 x₂) ⟫ ⟫
      lem03 : {t t₁ t₂ : bt (Color ∧ A)} {value₁ : A} {key₁ = key₂ : ℕ} (x : color t₂ ≡ Red) (x₁ : key₂ < key) (rbt : replacedRBTree key value t₁ t₂) →
            ((key₃ : ℕ) → key₃ < key → tr> key₃ t₁ → tr> key₃ t₂) → (key₃ : ℕ) → key₃ < key → (key₃ < key₂) ∧ tr> key₃ t ∧ tr> key₃ t₁ → (key₃ < key₂) ∧ tr> key₃ t ∧ tr> key₃ t₂
      lem03 {t} x x₁ rbt prev k3 x₃ x₂ = ⟪ proj1 x₂ , ⟪ proj1 (proj2 x₂) , prev _ x₃ (proj2 (proj2 x₂))  ⟫ ⟫
      lem04 : {t t₁ t₂ : bt (Color ∧ A)} {value₁ : A} {key₁ = key₂ : ℕ} (x : color t₂ ≡ Red) (x₁ : key < key₂) (rbt : replacedRBTree key value t₁ t₂) →
            ((key₃ : ℕ) → key₃ < key → tr> key₃ t₁ → tr> key₃ t₂) → (key₃ : ℕ) → key₃ < key → (key₃ < key₂) ∧ tr> key₃ t₁ ∧ tr> key₃ t → (key₃ < key₂) ∧ tr> key₃ t₂ ∧ tr> key₃ t
      lem04 {t} {t₁} {t₂} {v₁} x x₁ rbt prev k3 x₃ x₂ = ⟪ proj1 x₂ , ⟪ prev _ x₃ (proj1 (proj2 x₂))  , proj2 (proj2 x₂) ⟫ ⟫
      lem05 :  {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A} (x : color t₂ ≡ Red) (x₁ : color uncle ≡ Red) (x₂ : key < kp) (rbt : replacedRBTree key value t₁ t₂) →
            ((key₂ : ℕ) → key₂ < key → tr> key₂ t₁ → tr> key₂ t₂) → (key₂ : ℕ) → key₂ < key →
            (key₂ < kg) ∧ ((key₂ < kp) ∧ tr> key₂ t₁ ∧ tr> key₂ t) ∧ tr> key₂ uncle → (key₂ < kg) ∧ ((key₂ < kp) ∧ tr> key₂ t₂ ∧ tr> key₂ t) ∧ tr> key₂ (to-black uncle)
      lem05 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} x x₁ x₂ rbt prev k2 x₄ x₃ = ⟪ proj1 x₃ , 
        ⟪ ⟪ proj1 lem10 , ⟪ prev _ x₄ (proj1 (proj2 lem10)) , proj2 (proj2 lem10)  ⟫ ⟫  , tr>-to-black (proj2 (proj2 x₃)) ⟫ ⟫ where
          lem10 = proj1 (proj2 x₃)
      lem06 :  {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A} (x : color t₂ ≡ Red) (x₁ : color uncle ≡ Red) (x₂ : kp < key)
            (x₃ : key < kg) (rbt : replacedRBTree key value t₁ t₂) → ((key₂ : ℕ) → key₂ < key → tr> key₂ t₁ → tr> key₂ t₂) → (key₂ : ℕ) →
            key₂ < key → (key₂ < kg) ∧ ((key₂ < kp) ∧ tr> key₂ t ∧ tr> key₂ t₁) ∧ tr> key₂ uncle →
            (key₂ < kg) ∧ ((key₂ < kp) ∧ tr> key₂ t ∧ tr> key₂ t₂) ∧ tr> key₂ (to-black uncle)
      lem06 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} x x₁ x₂ x₃ rbt prev k2 x₄ x₅ = ⟪ proj1 x₅ , 
         ⟪ ⟪ proj1 lem10 , ⟪ proj1 (proj2 lem10) , prev _ x₄ (proj2 (proj2 lem10))  ⟫ ⟫ , tr>-to-black (proj2 (proj2 x₅)) ⟫ ⟫ where
          lem10 = proj1 (proj2  x₅)
      lem07 : {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A} (x : color t₂ ≡ Red) (x₁ : color uncle ≡ Red) (x₂ : kg < key)
            (x₃ : key < kp) (rbt : replacedRBTree key value t₁ t₂) → ((key₂ : ℕ) → key₂ < key → tr> key₂ t₁ → tr> key₂ t₂) →
            (key₂ : ℕ) → key₂ < key → (key₂ < kg) ∧ tr> key₂ uncle ∧ (key₂ < kp) ∧ tr> key₂ t₁ ∧ tr> key₂ t → (key₂ < kg) ∧
            tr> key₂ (to-black uncle) ∧ (key₂ < kp) ∧ tr> key₂ t₂ ∧ tr> key₂ t
      lem07 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} x x₁ x₂ x₃ rbt prev k2 x₄ x₅ = ⟪ proj1 x₅ , ⟪ tr>-to-black (proj1 (proj2 x₅)) , 
         ⟪ proj1 (proj2 (proj2 x₅)) , ⟪ prev _ x₄ (proj1 (proj2 (proj2 (proj2 x₅)))) , proj2 (proj2 (proj2 (proj2 x₅))) ⟫ ⟫ ⟫ ⟫
      lem08 : {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A} (x : color t₂ ≡ Red) (x₁ : color uncle ≡ Red) (x₂ : kp < key)
            (rbt : replacedRBTree key value t₁ t₂) → ((key₂ : ℕ) → key₂ < key → tr> key₂ t₁ → tr> key₂ t₂) → (key₂ : ℕ) →
            key₂ < key → (key₂ < kg) ∧ tr> key₂ uncle ∧ (key₂ < kp) ∧ tr> key₂ t ∧ tr> key₂ t₁ →
            (key₂ < kg) ∧ tr> key₂ (to-black uncle) ∧ (key₂ < kp) ∧ tr> key₂ t ∧ tr> key₂ t₂
      lem08 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} x x₁ x₂ rbt prev k2 x₄ x₅ = ⟪ proj1 x₅ , ⟪ tr>-to-black (proj1 (proj2 x₅)) , 
         ⟪ proj1 (proj2 (proj2 x₅)) , ⟪ proj1 (proj2 (proj2 (proj2 x₅))) , prev _ x₄ (proj2 (proj2 (proj2 (proj2 x₅)))) ⟫ ⟫ ⟫ ⟫
      lem09 :  {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A} (x : color t₂ ≡ Red) (x₁ : key < kp) (rbt : replacedRBTree key value t₁ t₂) →
            ((key₂ : ℕ) → key₂ < key → tr> key₂ t₁ → tr> key₂ t₂) → (key₂ : ℕ) → key₂ < key →
            (key₂ < kg) ∧ ((key₂ < kp) ∧ tr> key₂ t₁ ∧ tr> key₂ t) ∧ tr> key₂ uncle → (key₂ < kp) ∧ tr> key₂ t₂ ∧ (key₂ < kg) ∧ tr> key₂ t ∧ tr> key₂ uncle
      lem09 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} x x₁ rbt prev k2 x₄ x₅ = ⟪ proj1 lem10 , 
         ⟪ prev _ x₄ (proj1 (proj2 lem10)) , ⟪ proj1 x₅ , ⟪ proj2 (proj2 lem10) , proj2 (proj2 x₅) ⟫ ⟫ ⟫ ⟫ where
          lem10 = proj1 (proj2 x₅)
      lem11 : {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A} (x : color t₂ ≡ Red) (x₁ : kp < key) (rbt : replacedRBTree key value t₁ t₂) →
            ((key₂ : ℕ) → key₂ < key → tr> key₂ t₁ → tr> key₂ t₂) → (key₂ : ℕ) → key₂ < key → (key₂ < kg) ∧
            tr> key₂ uncle ∧ (key₂ < kp) ∧ tr> key₂ t ∧ tr> key₂ t₁ → (key₂ < kp) ∧ ((key₂ < kg) ∧ tr> key₂ uncle ∧ tr> key₂ t) ∧ tr> key₂ t₂
      lem11 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} x x₁ rbt prev k2 x₄ x₅ = ⟪ proj1 (proj2 (proj2 x₅)) , 
         ⟪ ⟪ proj1 x₅ , ⟪ proj1 (proj2 x₅) , proj1 (proj2 (proj2 (proj2 x₅))) ⟫ ⟫ , prev _ x₄ (proj2 (proj2 (proj2 (proj2 x₅)))) ⟫ ⟫ 
      lem12 : {t t₁ uncle : bt (Color ∧ A)} (t₂ t₃ : bt (Color ∧ A)) (kg kp kn : ℕ) {vg vp vn : A} (x : color t₃ ≡ Black)
            (x₁ : kp < key) (x₂ : key < kg) (rbt : replacedRBTree key value t₁ (node kn ⟪ Red , vn ⟫ t₂ t₃)) →
            ((key₂ : ℕ) → key₂ < key → tr> key₂ t₁ → (key₂ < kn) ∧ tr> key₂ t₂ ∧ tr> key₂ t₃) → (key₂ : ℕ) → key₂ < key →
            (key₂ < kg) ∧ ((key₂ < kp) ∧ tr> key₂ t ∧ tr> key₂ t₁) ∧ tr> key₂ uncle → (key₂ < kn) ∧
            ((key₂ < kp) ∧ tr> key₂ t ∧ tr> key₂ t₂) ∧ (key₂ < kg) ∧ tr> key₂ t₃ ∧ tr> key₂ uncle
      lem12 {t} {t₁} {uncle} t₂ t₃ kg kp kn {vg} {vp} {vn} x x₁ x₂ rbt prev k2 x₄ x₅ = ⟪ proj1 lem14 , ⟪ ⟪ proj1 lem15 , 
        ⟪ proj1 (proj2 lem15) , proj1 (proj2 lem14) ⟫ ⟫ , ⟪ proj1 x₅ , ⟪ proj2 (proj2 lem14) , proj2 (proj2 x₅) ⟫ ⟫ ⟫ ⟫ where
          lem15 = proj1 (proj2 x₅)
          lem14 : (k2 < kn ) ∧ tr> k2 t₂ ∧ tr> k2 t₃
          lem14 = prev _ x₄ (proj2 (proj2 lem15))
      lem13 :  {t t₁ uncle : bt (Color ∧ A)} (t₂ t₃ : bt (Color ∧ A)) (kg kp kn : ℕ) {vg vp vn : A} (x : color t₃ ≡ Black) (x₁ : kg < key) (x₂ : key < kp)
            (rbt : replacedRBTree key value t₁ (node kn ⟪ Red , vn ⟫ t₂ t₃)) → ((key₂ : ℕ) → key₂ < key → tr> key₂ t₁ → (key₂ < kn) ∧ tr> key₂ t₂ ∧ tr> key₂ t₃) →
            (key₂ : ℕ) → key₂ < key → (key₂ < kg) ∧ tr> key₂ uncle ∧ (key₂ < kp) ∧ tr> key₂ t₁ ∧ tr> key₂ t →
            (key₂ < kn) ∧ ((key₂ < kg) ∧ tr> key₂ uncle ∧ tr> key₂ t₂) ∧ (key₂ < kp) ∧ tr> key₂ t₃ ∧ tr> key₂ t
      lem13 {t} {t₁} {uncle} t₂ t₃ kg kp kn {vg} {vp} {vn} x x₁ x₂ rbt prev k2 x₄ x₅ = ⟪ proj1 lem14 , ⟪ ⟪ proj1 x₅ , 
        ⟪ proj1 (proj2 x₅) , proj1 (proj2 lem14) ⟫ ⟫ , ⟪ proj1 (proj2 (proj2 x₅)) , ⟪ proj2 (proj2 lem14) , proj2 (proj2 (proj2 (proj2 x₅))) ⟫ ⟫ ⟫ ⟫ where
          lem14 : (k2 < kn ) ∧ tr> k2 t₂ ∧ tr> k2 t₃
          lem14 = prev _ x₄ (proj1 (proj2 (proj2 (proj2 x₅))))

           

RB-repl→ti<  : {n : Level} {A : Set n}  → (tree repl : bt (Color ∧ A)) → (key key₁ : ℕ) → (value : A)
     → replacedRBTree key value tree repl → key < key₁ → tr< key₁ tree → tr< key₁ repl
RB-repl→ti<  {n} {A} tree repl key key₁ value rbr s1 s2 = RBTI-induction A tree tree repl key value refl rbr  
  {λ key value b a rbt → (key₁ : ℕ) → key < key₁ → tr< key₁ b  → tr< key₁ a}
     ⟪ (λ _ x _ →  ⟪ x , ⟪ tt , tt ⟫ ⟫  ) , ⟪ lem00 , ⟪ (λ {k} {v1} {ca} {t} {t1} {t2} → lem01 {k} {v1} {ca} {t} {t1} {t2} ) , ⟪ 
        (λ {k} {v1} {ca} {t} {t1} {t2} → lem02 {k} {v1} {ca} {t} {t1} {t2} ) , ⟪ 
        (λ {t} {t₁} {t₂} {v1} → lem03 {t} {t₁} {t₂} {v1} ) , ⟪ 
        (λ {t} {t₁} {t₂} {v₁} {key₁} → lem04 {t} {t₁} {t₂} {v₁} {key₁}  ) , ⟪ 
        (λ {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} → lem05 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp}) , ⟪ 
        (λ {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} → lem06 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} )  , ⟪ 
        (λ {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} → lem07 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp}  ) , ⟪ 
        (λ {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} → lem08 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp}) , ⟪ 
        (λ {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} → lem09 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} ) , ⟪ 
        (λ {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} → lem11 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} ) , ⟪ 
        (λ {t} {t₁} {uncle} → lem12 {t} {t₁} {uncle} ) , 
        (λ {t} {t₁} {uncle} → lem13 {t} {t₁} {uncle} ) 
        ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ key₁ s1 s2 where
      lem00 :  (ca : Color) (value₂ : A) (t t₁ : bt (Color ∧ A)) (key₂ : ℕ) → key < key₂ → (key < key₂) ∧ tr< key₂ t ∧ tr< key₂ t₁ → (key < key₂) ∧ tr< key₂ t ∧ tr< key₂ t₁
      lem00 ca v2 t t₁ k2 x ⟪ x₁ , ⟪ x₂ , x₃ ⟫ ⟫ = ⟪ x , ⟪ x₂ , x₃  ⟫ ⟫
      lem01 :   {k : ℕ} {v1 : A} {ca : Color} {t t1 t2 : bt (Color ∧ A)} (x : color t2 ≡ color t) (x₁ : k < key )
            (rbt : replacedRBTree key value t2 t) → ((key₂ : ℕ) → key < key₂ → tr< key₂ t2 → tr< key₂ t) → (key₂ : ℕ) → key < key₂ →
            (k < key₂ ) ∧ tr< key₂ t1 ∧ tr< key₂ t2 → (k < key₂ ) ∧ tr< key₂ t1 ∧ tr< key₂ t
      lem01 {k} {v1} {ca} {t} {t1} {t2} ceq x₁ rbt prev k2 x x₂  = ⟪ proj1 x₂ , ⟪ proj1 (proj2 x₂) , prev _ x (proj2 (proj2 x₂)) ⟫ ⟫
      lem02 : {k : ℕ} {v1 : A} {ca : Color} {t t1 t2 : bt (Color ∧ A)} (x : color t1 ≡ color t) (x₁ : key < k)
            (rbt : replacedRBTree key value t1 t) → ((key₂ : ℕ) → key < key₂ → tr< key₂ t1 → tr< key₂ t) →
            (key₂ : ℕ) → key < key₂ → (k < key₂) ∧ tr< key₂ t1 ∧ tr< key₂ t2 → (k < key₂) ∧ tr< key₂ t ∧ tr< key₂ t2
      lem02 {k} {v1} {ca} {t} {t1} {t2} ceq x₁ rbt prev k2 x x₂ = ⟪ proj1 x₂ , ⟪ prev _ x (proj1 (proj2 x₂)) , proj2 (proj2 x₂) ⟫ ⟫
      lem03 : {t t₁ t₂ : bt (Color ∧ A)} {value₁ : A} {key₁ = key₂ : ℕ} (x : color t₂ ≡ Red) (x₁ : key₂ < key) (rbt : replacedRBTree key value t₁ t₂) →
            ((key₃ : ℕ) → key < key₃ → tr< key₃ t₁ → tr< key₃ t₂) → (key₃ : ℕ) → key < key₃ → (key₂ < key₃) ∧ tr< key₃ t ∧ tr< key₃ t₁ → (key₂ < key₃) ∧ tr< key₃ t ∧ tr< key₃ t₂
      lem03 {t} x x₁ rbt prev k3 x₃ x₂ = ⟪ proj1 x₂ , ⟪ proj1 (proj2 x₂) , prev _ x₃ (proj2 (proj2 x₂))  ⟫ ⟫
      lem04 : {t t₁ t₂ : bt (Color ∧ A)} {value₁ : A} {key₁ : ℕ} (x : color t₂ ≡ Red) (x₁ : key < key₁) (rbt : replacedRBTree key value t₁ t₂) →
            ((key₃ : ℕ) → key < key₃ → tr< key₃ t₁ → tr< key₃ t₂) → (key₃ : ℕ) → key < key₃ → (key₁ < key₃) ∧ tr< key₃ t₁ ∧ tr< key₃ t → (key₁ < key₃) ∧ tr< key₃ t₂ ∧ tr< key₃ t
      lem04 {t} {t₁} {t₂} {v₁} x x₁ rbt prev k3 x₃ x₂ = ⟪ proj1 x₂ , ⟪ prev _ x₃ (proj1 (proj2 x₂))  , proj2 (proj2 x₂) ⟫ ⟫
      lem05 :  {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A} (x : color t₂ ≡ Red) (x₁ : color uncle ≡ Red) (x₂ : key < kp) (rbt : replacedRBTree key value t₁ t₂) →
            ((key₂ : ℕ) → key < key₂ → tr< key₂ t₁ → tr< key₂ t₂) → (key₂ : ℕ) → key < key₂ → (kg < key₂) ∧
            ((kp < key₂) ∧ tr< key₂ t₁ ∧ tr< key₂ t) ∧ tr< key₂ uncle → (kg < key₂) ∧ ((kp < key₂) ∧ tr< key₂ t₂ ∧ tr< key₂ t) ∧ tr< key₂ (to-black uncle)
      lem05 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} x x₁ x₂ rbt prev k2 x₄ x₃ = ⟪ proj1 x₃ , 
        ⟪ ⟪ proj1 lem10 , ⟪ prev _ x₄ (proj1 (proj2 lem10)) , proj2 (proj2 lem10)  ⟫ ⟫  , tr<-to-black (proj2 (proj2 x₃)) ⟫ ⟫ where
          lem10 = proj1 (proj2 x₃)
      lem06 :  {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A} (x : color t₂ ≡ Red) (x₁ : color uncle ≡ Red) (x₂ : kp < key)
            (x₃ : key < kg) (rbt : replacedRBTree key value t₁ t₂) → ((key₂ : ℕ) → key < key₂ → tr< key₂ t₁ → tr< key₂ t₂) → (key₂ : ℕ) → key < key₂ →
            (kg < key₂) ∧ ((kp < key₂) ∧ tr< key₂ t ∧ tr< key₂ t₁) ∧ tr< key₂ uncle → (kg < key₂) ∧ ((kp < key₂) ∧ tr< key₂ t ∧ tr< key₂ t₂) ∧ tr< key₂ (to-black uncle)
      lem06 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} x x₁ x₂ x₃ rbt prev k2 x₄ x₅ = ⟪ proj1 x₅ , 
         ⟪ ⟪ proj1 lem10 , ⟪ proj1 (proj2 lem10) , prev _ x₄ (proj2 (proj2 lem10))  ⟫ ⟫ , tr<-to-black (proj2 (proj2 x₅)) ⟫ ⟫ where
          lem10 = proj1 (proj2  x₅)
      lem07 : {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A} (x : color t₂ ≡ Red) (x₁ : color uncle ≡ Red) (x₂ : kg < key)
            (x₃ : key < kp) (rbt : replacedRBTree key value t₁ t₂) → ((key₂ : ℕ) → key < key₂ → tr< key₂ t₁ → tr< key₂ t₂) →
            (key₂ : ℕ) → key < key₂ → (kg < key₂) ∧ tr< key₂ uncle ∧ (kp < key₂) ∧ tr< key₂ t₁ ∧ tr< key₂ t → (kg < key₂) ∧
            tr< key₂ (to-black uncle) ∧ (kp < key₂) ∧ tr< key₂ t₂ ∧ tr< key₂ t
      lem07 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} x x₁ x₂ x₃ rbt prev k2 x₄ x₅ = ⟪ proj1 x₅ , ⟪ tr<-to-black (proj1 (proj2 x₅)) , 
         ⟪ proj1 (proj2 (proj2 x₅)) , ⟪ prev _ x₄ (proj1 (proj2 (proj2 (proj2 x₅)))) , proj2 (proj2 (proj2 (proj2 x₅))) ⟫ ⟫ ⟫ ⟫
      lem08 : {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A} (x : color t₂ ≡ Red) (x₁ : color uncle ≡ Red) (x₂ : kp < key)
            (rbt : replacedRBTree key value t₁ t₂) → ((key₂ : ℕ) → key < key₂ → tr< key₂ t₁ → tr< key₂ t₂) →
            (key₂ : ℕ) → key < key₂ → (kg < key₂) ∧ tr< key₂ uncle ∧ (kp < key₂) ∧ tr< key₂ t ∧ tr< key₂ t₁ →
            (kg < key₂) ∧ tr< key₂ (to-black uncle) ∧ (kp < key₂) ∧ tr< key₂ t ∧ tr< key₂ t₂
      lem08 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} x x₁ x₂ rbt prev k2 x₄ x₅ = ⟪ proj1 x₅ , ⟪ tr<-to-black (proj1 (proj2 x₅)) , 
         ⟪ proj1 (proj2 (proj2 x₅)) , ⟪ proj1 (proj2 (proj2 (proj2 x₅))) , prev _ x₄ (proj2 (proj2 (proj2 (proj2 x₅)))) ⟫ ⟫ ⟫ ⟫
      lem09 :  {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A} (x : color t₂ ≡ Red) (x₁ : key < kp) (rbt : replacedRBTree key value t₁ t₂) →
            ((key₂ : ℕ) → key < key₂ → tr< key₂ t₁ → tr< key₂ t₂) → (key₂ : ℕ) → key < key₂ → (kg < key₂) ∧
            ((kp < key₂) ∧ tr< key₂ t₁ ∧ tr< key₂ t) ∧ tr< key₂ uncle → (kp < key₂) ∧ tr< key₂ t₂ ∧ (kg < key₂) ∧ tr< key₂ t ∧ tr< key₂ uncle
      lem09 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} x x₁ rbt prev k2 x₄ x₅ = ⟪ proj1 lem10 , 
         ⟪ prev _ x₄ (proj1 (proj2 lem10)) , ⟪ proj1 x₅ , ⟪ proj2 (proj2 lem10) , proj2 (proj2 x₅) ⟫ ⟫ ⟫ ⟫ where
          lem10 = proj1 (proj2 x₅)
      lem11 : {t t₁ t₂ uncle : bt (Color ∧ A)} {kg kp : ℕ} {vg vp : A} (x : color t₂ ≡ Red) (x₁ : kp < key) (rbt : replacedRBTree key value t₁ t₂) →
            ((key₂ : ℕ) → key < key₂ → tr< key₂ t₁ → tr< key₂ t₂) → (key₂ : ℕ) → key < key₂ → (kg < key₂) ∧
            tr< key₂ uncle ∧ (kp < key₂) ∧ tr< key₂ t ∧ tr< key₂ t₁ → (kp < key₂) ∧ ((kg < key₂) ∧ tr< key₂ uncle ∧ tr< key₂ t) ∧ tr< key₂ t₂
      lem11 {t} {t₁} {t₂} {uncle} {kg} {kp} {vg} {vp} x x₁ rbt prev k2 x₄ x₅ = ⟪ proj1 (proj2 (proj2 x₅)) , 
         ⟪ ⟪ proj1 x₅ , ⟪ proj1 (proj2 x₅) , proj1 (proj2 (proj2 (proj2 x₅))) ⟫ ⟫ , prev _ x₄ (proj2 (proj2 (proj2 (proj2 x₅)))) ⟫ ⟫ 
      lem12 : {t t₁ uncle : bt (Color ∧ A)} (t₂ t₃ : bt (Color ∧ A)) (kg kp kn : ℕ) {vg vp vn : A} (x : color t₃ ≡ Black) (x₁ : kp < key) (x₂ : key < kg)
            (rbt : replacedRBTree key value t₁ (node kn ⟪ Red , vn ⟫ t₂ t₃)) → ((key₂ : ℕ) → key < key₂ → tr< key₂ t₁ → (kn < key₂) ∧ tr< key₂ t₂ ∧ tr< key₂ t₃) →
            (key₂ : ℕ) → key < key₂ → (kg < key₂) ∧ ((kp < key₂) ∧ tr< key₂ t ∧ tr< key₂ t₁) ∧ tr< key₂ uncle →
            (kn < key₂) ∧ ((kp < key₂) ∧ tr< key₂ t ∧ tr< key₂ t₂) ∧ (kg < key₂) ∧ tr< key₂ t₃ ∧ tr< key₂ uncle
      lem12 {t} {t₁} {uncle} t₂ t₃ kg kp kn {vg} {vp} {vn} x x₁ x₂ rbt prev k2 x₄ x₅ = ⟪ proj1 lem14 , ⟪ ⟪ proj1 lem15 , 
        ⟪ proj1 (proj2 lem15) , proj1 (proj2 lem14) ⟫ ⟫ , ⟪ proj1 x₅ , ⟪ proj2 (proj2 lem14) , proj2 (proj2 x₅) ⟫ ⟫ ⟫ ⟫ where
          lem15 = proj1 (proj2 x₅)
          lem14 : (kn < k2 ) ∧ tr< k2 t₂ ∧ tr< k2 t₃
          lem14 = prev _ x₄ (proj2 (proj2 lem15))
      lem13 :  {t t₁ uncle : bt (Color ∧ A)} (t₂ t₃ : bt (Color ∧ A)) (kg kp kn : ℕ) {vg vp vn : A} (x : color t₃ ≡ Black) (x₁ : kg < key) (x₂ : key < kp)
            (rbt : replacedRBTree key value t₁ (node kn ⟪ Red , vn ⟫ t₂ t₃)) → ((key₂ : ℕ) → key < key₂ → tr< key₂ t₁ → (kn < key₂) ∧ tr< key₂ t₂ ∧ tr< key₂ t₃) → (key₂ : ℕ) →
            key < key₂ → (kg < key₂) ∧ tr< key₂ uncle ∧ (kp < key₂) ∧ tr< key₂ t₁ ∧ tr< key₂ t →
            (kn < key₂) ∧ ((kg < key₂) ∧ tr< key₂ uncle ∧ tr< key₂ t₂) ∧ (kp < key₂) ∧ tr< key₂ t₃ ∧ tr< key₂ t
      lem13 {t} {t₁} {uncle} t₂ t₃ kg kp kn {vg} {vp} {vn} x x₁ x₂ rbt prev k2 x₄ x₅ = ⟪ proj1 lem14 , ⟪ ⟪ proj1 x₅ , 
        ⟪ proj1 (proj2 x₅) , proj1 (proj2 lem14) ⟫ ⟫ , ⟪ proj1 (proj2 (proj2 x₅)) , ⟪ proj2 (proj2 lem14) , proj2 (proj2 (proj2 (proj2 x₅))) ⟫ ⟫ ⟫ ⟫ where
          lem14 : (kn < k2 ) ∧ tr< k2 t₂ ∧ tr< k2 t₃
          lem14 = prev _ x₄ (proj1 (proj2 (proj2 (proj2 x₅))))

RBI-child-replaced : {n : Level} {A : Set n} (tr : bt (Color ∧ A)) (key : ℕ) →  RBtreeInvariant tr → RBtreeInvariant (child-replaced key tr)
RBI-child-replaced {n} {A} leaf key rbi = rbi
RBI-child-replaced {n} {A} (node key₁ value tr tr₁) key rbi with <-cmp key key₁
... | tri< a ¬b ¬c = RBtreeLeftDown _ _ rbi
... | tri≈ ¬a b ¬c = rbi
... | tri> ¬a ¬b c = RBtreeRightDown _ _ rbi

-- replacedRBTree→replacedTree : {n : Level} {A : Set n} (key : ℕ) (value : A) (before after : bt (Color ∧ A) ) 
--    → replacedRBTree key value before after → {ca : Color} → replacedTree key ⟪ ca , value ⟫ before after
