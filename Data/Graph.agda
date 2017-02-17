module Graph {ℓ} (Node Edge : Set ℓ) where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat using (_-_)
open import Agda.Builtin.Equality using (_≡_)
import Data.AVL
open import Data.Bool using (Bool; not)
open import Data.Fin as Fin using (Fin; zero; suc; #_; toℕ; fromℕ)
open import Data.List as List using (List; _∷_; []; [_]; filter; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat as Nat using (ℕ; suc; pred; _≥_; _≟_)
open import Data.Product as Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Function as Fn using (_∘_; _$_)
import Level as L
import Relation.Binary
open import Relation.Nullary.Decidable using (⌊_⌋)

GraphT : Set (L.suc ℓ)
GraphT =  Set ℓ → Set ℓ → ℕ → Set ℓ

-- A Context is a node, identified by `id`, from a graph with at
-- most `n` nodes. It includes its incoming and outgoing edges
-- from its parent graph along with labels for them and itself.
record Context {n : ℕ} (id : Fin n) : Set ℓ where
  constructor context
  field
    -- Incoming edges and labels.
    preds : List (Edge × Fin n)
    label : Node
    -- Outgoing edges and labels.
    succs : List (Edge × Fin n)

infixr 3 _&_

-- A Decomp is a decomposition of a graph into a Context and the
-- graph that is left when all the elements of the context are
-- removed.
data Decomp (G : ℕ → Set ℓ) : ℕ → Set ℓ where
  ∅ : ∀ {n} → Decomp G n
  _&_ : ∀ {n} {id : Fin n} (c : Context id) (g : G n) → Decomp G n

record Graph (G : ℕ → Set ℓ) : Set ℓ where
  field
    -- The empty graph for the given size.
    empty : ∀ {n} → G n
    -- Inserts a new node with id `n`, growing the graph. Useful
    -- for building a graph with new contexts.
    insert : ∀ {n} → Context (fromℕ n) → G n → G (suc n)
    -- Inserts a node into the graph without growing it. Overwrites
    -- if the identified node is already in the graph. Useful when
    -- reconstructing a graph that has been `match`ed against.
    reinsert : ∀ {n} {id : Fin n} → Context id → G n → G n
    -- Decomposes the given graph with an arbitrary node. Yields the
    -- empty decomposition if no nodes are present.
    matchAny : ∀ {n} → G n → Decomp G n
    -- Decomposes the given graph with the given node. A returned
    -- context is guaranteed to contain all edges in and out of that
    -- node, while the returned graph will contain none of them.
    match : ∀ {n} (a : Fin n) → G n → Decomp G n
    -- Remove the given node from the graph, decrementing the ids
    -- of all nodes larger than it and shrinking the graph.
    remove : ∀ {n} (id : Fin n) → G n → G (pred n)

  isEmpty : ∀ {n} → G n → Bool
  isEmpty g with matchAny g
  ...          | ∅ = true
  ...          | _ & _ = false

-- Mapping functions for contexts and graphs. Particularly useful when
-- needing to move nodes and edges between graphs of different sizes.
-- f : a transformation on the upper bound of node ids
-- f-fin : a type-consistent transformation on the node ids themselves
module Maps (f : ℕ → ℕ) (f-fin : ∀ {n} → Fin n → Fin (f n)) where
  mapEdge : ∀ {n} → Edge × Fin n → Edge × Fin (f n)
  mapEdge p = Product.map Fn.id f-fin p
  mapContext : ∀ {n} {n-fin : Fin n} → Context n-fin → Context (f-fin n-fin)
  mapContext {_} {n-fin} ctxt-n = ctxt-f
    where
    open Context ctxt-n
    ctxt-f : Context (f-fin n-fin)
    preds ctxt-f = List.map mapEdge preds
    label ctxt-f = label
    succs ctxt-f = List.map mapEdge succs

open Graph {{...}} public

private
  -- Implements the Graph interface with AVL trees. Keeps contexts
  -- ordered by id, re-ordering insertions to maintain the invariant
  -- that the (internal) context for `id` only refers to nodes with
  -- smaller ids. This allows searches for edges relating to nodes
  -- with large ids to be fast (though better, more complicated
  -- representations certainly exist).
  module Impl where
    open import Data.Fin.Properties as FinP
    open import Relation.Binary using (module StrictTotalOrder)
    import Data.AVL
    module AVL (max : ℕ) = Data.AVL Context
         (StrictTotalOrder.isStrictTotalOrder (FinP.strictTotalOrder max))

    module ImplMaps (f : ℕ → ℕ) (f-fin : ∀ {n} → Fin n → Fin (f n)) where
      open Maps f f-fin
      mapKV : ∀ {n} → AVL.KV n → AVL.KV (f n)
      mapKV kv = Product.map f-fin mapContext kv
      mapTree : ∀ {n} → AVL.Tree n → AVL.Tree (f n)
      mapTree {n} t = t-f
        where
        l = AVL.toList n t
        l-f = List.map mapKV l
        t-f = AVL.fromList (f n) l-f

    AVLGraph : Graph AVL.Tree
    empty {{AVLGraph}} {n} = AVL.empty n
    insert {{AVLGraph}} {n} c g =
      AVL.insert (suc n) (fromℕ n) c (ImplMaps.mapTree suc Fin.suc g)
    reinsert {{AVLGraph}} {n} {id} c g = AVL.insert n id c g
    matchAny {{AVLGraph}} {n} g with AVL.initLast n g
    ...                            | just (g' , (_ , c)) = c & g'
    ...                            | nothing = ∅
    match {{AVLGraph}} id g = {!!}
    remove {{AVLGraph}} id g = {!!}
