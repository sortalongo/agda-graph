module Graph {ℓ} (Node Edge : Set ℓ) where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat using (_-_)
open import Agda.Builtin.Equality using (_≡_)
import Data.AVL
open import Data.Bool using (Bool; not)
open import Data.Fin as Fin using (Fin; zero; suc; #_; toℕ)
open import Data.List using (List; _∷_; []; [_]; filter; map)
open import Data.Nat as Nat using (ℕ; suc; pred; _≥_; _≟_)
open import Data.Product as Product using (_×_; _,_)
open import Data.String using (String)
open import Function using (_∘_)
import Level as L
import Relation.Binary
open import Relation.Nullary.Decidable using (⌊_⌋)

GraphT : Set (L.suc ℓ)
GraphT =  Set ℓ → Set ℓ → ℕ → Set ℓ

record Context (n : ℕ) : Set ℓ where
  constructor context
  field
    predecessors : List (Edge × Fin n)
    label : Node
    successors : List (Edge × Fin n)

infixr 3 _&_

data Decomp (G : ℕ → Set ℓ) : ℕ → Set ℓ where
  ∅ : Decomp G 0
  _&_ : ∀ {n} (c : Context n) (g : G n) → Decomp G (suc n)

record Graph (G : ℕ → Set ℓ) : Set ℓ where
  field
    empty : G 0
    insert : ∀ {n} → Context n → G n → G (suc n)
    delete : ∀ {n} → ℕ → G n → G (pred n)
    isEmpty : ∀ {n} → G n → Bool
    matchAny : ∀ {n} → G n → Decomp G n
    match : ∀ {n} (a : Fin n) → G n → Decomp G n

open Graph {{...}} public

private
  module Impl where
    data Impl : ℕ → Set ℓ where
      ∅ : Impl 0
      _&_ : ∀ {n} → Context n → Impl n → Impl (suc n)
    open Impl
    _⟦_⟧ : ∀ {n} → Impl n → (f : Fin n) → Context (n - toℕ f - 1)
    _⟦_⟧ ∅ ()
    _⟦_⟧ {suc 0} (c & ∅) Fin.zero = c
    _⟦_⟧ {suc n} (c & g) Fin.zero = c
    _⟦_⟧ {suc n} (_ & g) (Fin.suc f) = c where
         c : Context (n - toℕ f - 1)
         c = g ⟦ f ⟧

    record ExtractedContext (n : ℕ) : Set ℓ where
      field
        predecessors : List (Edge × Fin n)
        node : Fin n
        successors : List (Edge × Fin n)
      extract : Fin n → Context n
              → ExtractedContext n × Context (pred n)
      extract f c = (extracted , decremented)
        where
        open Context renaming
          (predecessors to cpreds; successors to csuccs)
        filtfn : Edge × Fin n → Bool
        filtfn (_ , f') = ⌊ (toℕ f ≟ toℕ f') ⌋
        extracted : ExtractedContext n
        predecessors extracted = filter filtfn (cpreds c)
        node extracted = f
        successors extracted = filter filtfn (csuccs c)
        decr : Edge × Fin n → Edge × Fin (pred n)
        decr (e , Fin.zero) = e , Fin.zero
        decr (e , Fin.suc f') = e , f'
        decremented : Context (pred n)
        cpreds decremented = ((map decr) ∘ (filter (not ∘ filtfn))) (cpreds c)
        label decremented = label c
        csuccs decremented = filter (not ∘ filtfn) (csuccs c)
      merge : ExtractedContext n → ExtractedContext (suc n)
            → ExtractedContext (suc n)
      merge x x' = {!!}
    open Decomp renaming (∅ to D∅; _&_ to _D&_)
    graph-list : Graph Impl
    empty {{graph-list}} = ∅
    insert {{graph-list}} {n} c g = c & g
    delete {{graph-list}} {n} i g = {!!}
    isEmpty {{graph-list}} {0} g = true
    isEmpty {{graph-list}} {_} g = false
    matchAny {{graph-list}} {0} ∅ = D∅
    matchAny {{graph-list}} {suc n} (c & g) = c D& g
    match {{graph-list}} {0} ()
    match {{graph-list}} {n} Fin.zero (c & g) = c D& g 
    match {{graph-list}} {n} (Fin.suc f) (c-outer & g) = {!
        let c-match D& g = match f g
            c-outer' = 
        in c-outer' D& (c-match & g)!}
    
