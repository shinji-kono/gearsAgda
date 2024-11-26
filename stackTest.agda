open import Level renaming (suc to succ ; zero to Zero )
module stackTest where

open import stack

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core
open import Data.Nat
open import Function


open SingleLinkedStack
open Stack

----
--
-- proof of properties ( concrete cases )
--

test01 : {n : Level } {a : Set n} -> SingleLinkedStack a -> Maybe a -> Bool {n}
test01 stack _ with (top stack)
...                  | (Just _) = True
...                  | Nothing  = False


test02 : {n : Level } {a : Set n} -> SingleLinkedStack a -> Bool
test02 stack = popSingleLinkedStack stack test01

test03 : {n : Level } {a : Set n} -> a ->  Bool
test03 v = pushSingleLinkedStack emptySingleLinkedStack v test02

-- after a push and a pop, the stack is empty
lemma : {n : Level} {A : Set n} {a : A} -> test03 a ≡ False
lemma = refl

testStack01 : {n m : Level } {a : Set n} -> a -> Bool {m}
testStack01 v = pushStack createSingleLinkedStack v (
   \s -> popStack s (\s1 d1 -> True))

-- after push 1 and 2, pop2 get 1 and 2

testStack02 : {m : Level } ->  ( Stack  ℕ (SingleLinkedStack ℕ) -> Bool {m} ) -> Bool {m}
testStack02 cs = pushStack createSingleLinkedStack 1 (
   \s -> pushStack s 2 cs)


testStack031 : (d1 d2 : ℕ ) -> Bool {Zero}
testStack031 2 1 = True
testStack031 _ _ = False

testStack032 : (d1 d2 : Maybe ℕ) -> Bool {Zero}
testStack032  (Just d1) (Just d2) = testStack031 d1 d2
testStack032  _ _ = False

testStack03 : {m : Level } -> Stack  ℕ (SingleLinkedStack ℕ) -> ((Maybe ℕ) -> (Maybe ℕ) -> Bool {m} ) -> Bool {m}
testStack03 s cs = pop2Stack s (
   \s d1 d2 -> cs d1 d2 )

testStack04 : Bool
testStack04 = testStack02 (\s -> testStack03 s testStack032)

testStack05 : testStack04 ≡ True
testStack05 = refl

testStack06 : {m : Level } -> Maybe (Element ℕ)
testStack06 = pushStack createSingleLinkedStack 1 (
   \s -> pushStack s 2 (\s -> top (stack s)))

testStack07 : {m : Level } -> Maybe (Element ℕ)
testStack07 = pushSingleLinkedStack emptySingleLinkedStack 1 (
   \s -> pushSingleLinkedStack s 2 (\s -> top s))

testStack08 = pushSingleLinkedStack emptySingleLinkedStack 1 
   $ \s -> pushSingleLinkedStack s 2 
   $ \s -> pushSingleLinkedStack s 3 
   $ \s -> pushSingleLinkedStack s 4 
   $ \s -> pushSingleLinkedStack s 5 
   $ \s -> top s

------
--
-- proof of properties with indefinite state of stack
--
-- this should be proved by properties of the stack inteface, not only by the implementation,
--    and the implementation have to provides the properties.
--
--    we cannot write "s ≡ s3", since level of the Set does not fit , but use stack s ≡ stack s3 is ok.
--    anyway some implementations may result s != s3
--  

stackInSomeState : {l m : Level } {D : Set l} {t : Set m } (s : SingleLinkedStack D ) -> Stack {l} {m} D {t}  ( SingleLinkedStack  D )
stackInSomeState s =  record { stack = s ; stackMethods = singleLinkedStackSpec }

push->push->pop2 : {l : Level } {D : Set l} (x y : D ) (s : SingleLinkedStack D ) ->
    pushStack ( stackInSomeState s )  x ( \s1 -> pushStack s1 y ( \s2 -> pop2Stack s2 ( \s3 y1 x1 -> (Just x ≡ x1 ) ∧ (Just y ≡ y1 ) ) ))
push->push->pop2 {l} {D} x y s = record { pi1 = refl ; pi2 = refl }


-- id : {n : Level} {A : Set n} -> A -> A
-- id a = a

-- push a, n times

n-push : {n : Level} {A : Set n} {a : A} -> ℕ -> SingleLinkedStack A -> SingleLinkedStack A
n-push zero s            = s
n-push {l} {A} {a} (suc n) s = pushSingleLinkedStack (n-push {l} {A} {a} n s) a (\s -> s ) 

n-pop :  {n : Level}{A : Set n} {a : A} -> ℕ -> SingleLinkedStack A -> SingleLinkedStack A
n-pop zero    s         = s
n-pop  {_} {A} {a} (suc n) s = popSingleLinkedStack (n-pop {_} {A} {a} n s) (\s _ -> s )

open ≡-Reasoning

push-pop-equiv : {n : Level} {A : Set n} {a : A} (s : SingleLinkedStack A) -> (popSingleLinkedStack (pushSingleLinkedStack s a (\s -> s)) (\s _ -> s) ) ≡ s
push-pop-equiv s = refl

push-and-n-pop : {n : Level} {A : Set n} {a : A} (n : ℕ) (s : SingleLinkedStack A) -> n-pop {_} {A} {a} (suc n) (pushSingleLinkedStack s a id) ≡ n-pop {_} {A} {a} n s
push-and-n-pop zero s            = refl
push-and-n-pop {_} {A} {a} (suc n) s = begin
   n-pop {_} {A} {a} (suc (suc n)) (pushSingleLinkedStack s a id)
  ≡⟨ refl ⟩
   popSingleLinkedStack (n-pop {_} {A} {a} (suc n) (pushSingleLinkedStack s a id)) (\s _ -> s)
  ≡⟨ cong (\s -> popSingleLinkedStack s (\s _ -> s )) (push-and-n-pop n s) ⟩ 
   popSingleLinkedStack (n-pop {_} {A} {a} n s) (\s _ -> s)
  ≡⟨ refl ⟩
    n-pop {_} {A} {a} (suc n) s
  ∎
  

n-push-pop-equiv : {n : Level} {A : Set n} {a : A} (n : ℕ) (s : SingleLinkedStack A) -> (n-pop {_} {A} {a} n (n-push {_} {A} {a} n s)) ≡ s
n-push-pop-equiv zero s            = refl
n-push-pop-equiv {_} {A} {a} (suc n) s = begin
    n-pop {_} {A} {a} (suc n) (n-push (suc n) s)
  ≡⟨ refl ⟩
    n-pop {_} {A} {a} (suc n) (pushSingleLinkedStack (n-push n s) a (\s -> s))
  ≡⟨ push-and-n-pop n (n-push n s)  ⟩
    n-pop {_} {A} {a} n (n-push n s)
  ≡⟨ n-push-pop-equiv n s ⟩
    s
  ∎


n-push-pop-equiv-empty : {n : Level} {A : Set n} {a : A} -> (n : ℕ) -> n-pop {_} {A} {a} n (n-push {_} {A} {a} n emptySingleLinkedStack)  ≡ emptySingleLinkedStack
n-push-pop-equiv-empty n = n-push-pop-equiv n emptySingleLinkedStack
