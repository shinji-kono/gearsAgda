open import Level renaming (suc to succ ; zero to Zero )
module Queue where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core
open import Data.Nat

data Maybe {n : Level } (a : Set n) : Set n where
  Nothing : Maybe a
  Just    : a -> Maybe a

data Bool {n : Level }: Set n where
  True : Bool
  False : Bool


record QueueMethods {n m : Level} (a : Set n) {t : Set m} (queueImpl : Set n) : Set (m Level.⊔ n) where
  field
    put   : queueImpl -> a -> (queueImpl -> t) -> t
    take  : queueImpl -> (queueImpl -> Maybe a -> t) -> t
    clear : queueImpl -> (queueImpl -> t) -> t
open QueueMethods

record Queue {n m : Level} (a : Set n) {t : Set m} (qu : Set n) : Set (m Level.⊔ n) where
  field
    queue : qu
    queueMethods : QueueMethods {n} {m} a {t} qu
  putQueue : a -> (Queue a qu -> t) -> t
  putQueue a next = put (queueMethods) (queue) a (\q1 -> next record {queue = q1 ; queueMethods = queueMethods})
  takeQueue : (Queue a qu -> Maybe a -> t) -> t
  takeQueue next = take (queueMethods) (queue) (\q1 d1 -> next record {queue = q1 ; queueMethods = queueMethods} d1)
  clearQueue : (Queue a qu -> t) -> t
  clearQueue next = clear (queueMethods) (queue) (\q1 -> next record {queue = q1 ; queueMethods = queueMethods})
open Queue



record Element {n : Level} (a : Set n) : Set n where
  inductive
  constructor cons
  field
    datum : a  -- `data` is reserved by Agda.
    next : Maybe (Element a)
open Element


record SingleLinkedQueue {n : Level} (a : Set n) : Set n where
  field
    top : Maybe (Element a)
    last : Maybe (Element a)
open SingleLinkedQueue


{-# TERMINATING #-}
reverseElement : {n : Level} {a : Set n} -> Element a -> Maybe (Element a) -> Element a
reverseElement el Nothing with next el
... | Just el1 = reverseElement el1 (Just rev)
  where
    rev = cons (datum el) Nothing
... | Nothing = el
reverseElement el (Just el0) with next el
... | Just el1 = reverseElement el1 (Just (cons (datum el) (Just el0)))
... | Nothing = (cons (datum el) (Just el0))


{-# TERMINATING #-}
putSingleLinkedQueue : {n m : Level} {t : Set m} {a : Set n} -> SingleLinkedQueue a -> a -> (Code : SingleLinkedQueue a -> t) -> t
putSingleLinkedQueue queue a cs with top queue
... | Just te = cs queue1
  where
    re = reverseElement te Nothing
    ce = cons a (Just re)
    commit = reverseElement ce Nothing
    queue1 = record queue {top = Just commit}
... | Nothing = cs queue1
  where
    cel = record {datum = a ; next = Nothing}
    queue1 = record {top = Just cel ; last = Just cel}

{-# TERMINATING #-}
takeSingleLinkedQueue : {n m : Level} {t : Set m} {a : Set n} -> SingleLinkedQueue a -> (Code : SingleLinkedQueue a -> (Maybe a) -> t) -> t
takeSingleLinkedQueue queue cs with (top queue)
... | Just te = cs record {top = (next te) ; last = Just (lastElement te)} (Just (datum te))
  where
    lastElement : {n : Level} {a : Set n} -> Element a -> Element a
    lastElement el with next el
    ... | Just el1 = lastElement el1
    ... | Nothing = el
... | Nothing = cs queue Nothing

clearSingleLinkedQueue : {n m : Level} {t : Set m} {a : Set n} -> SingleLinkedQueue a -> (SingleLinkedQueue a -> t) -> t
clearSingleLinkedQueue queue cs = cs (record {top = Nothing ; last = Nothing})


emptySingleLinkedQueue : {n : Level} {a : Set n} -> SingleLinkedQueue a
emptySingleLinkedQueue = record {top = Nothing ; last = Nothing}

singleLinkedQueueSpec : {n m : Level } {t : Set m } {a : Set n} -> QueueMethods {n} {m} a {t} (SingleLinkedQueue a)
singleLinkedQueueSpec = record {
                                    put = putSingleLinkedQueue
                                  ; take  = takeSingleLinkedQueue
                                  ; clear = clearSingleLinkedQueue
                                }


createSingleLinkedQueue : {n m : Level} {t : Set m} {a : Set n} -> Queue {n} {m} a {t} (SingleLinkedQueue a)
createSingleLinkedQueue = record {
  queue = emptySingleLinkedQueue ;
  queueMethods = singleLinkedQueueSpec
  }


check1 = putSingleLinkedQueue emptySingleLinkedQueue 1 (\q1 -> putSingleLinkedQueue q1 2 (\q2 -> putSingleLinkedQueue q2 3 (\q3 -> putSingleLinkedQueue q3 4 (\q4 -> putSingleLinkedQueue q4 5 (\q5 -> q5)))))


check2 = putSingleLinkedQueue emptySingleLinkedQueue 1 (\q1 -> putSingleLinkedQueue q1 2 (\q2 -> putSingleLinkedQueue q2 3 (\q3 -> putSingleLinkedQueue q3 4 (\q4 -> takeSingleLinkedQueue q4 (\q d -> q)))))


test01 : {n : Level } {a : Set n} -> SingleLinkedQueue a -> Maybe a -> Bool {n}
test01 queue _ with (top queue)
...                  | (Just _) = True
...                  | Nothing  = False
