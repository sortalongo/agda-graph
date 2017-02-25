module Data.Graph {ℓ} (Node Edge : Set ℓ) where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat using (_-_)
open import Agda.Builtin.Equality using (_≡_)
import Data.AVL
open import Data.Bool using (Bool; not)
open import Data.Fin as Fin using (Fin; zero; suc; #_; toℕ; fromℕ)
open import Data.List as List using (List; _∷_; []; [_]; filter; map; _++_)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat as Nat using (ℕ; suc; pred; _≥_)
open import Data.Product as Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Function as Fn using (_∘_; _$_; case_of_)
import Level as L
import Relation.Binary
open import Relation.Nullary.Decidable using (⌊_⌋)

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
module Contexts where
  open Context
  merge : ∀ {n} {id : Fin n} → Context id → Context id → Context id
  merge c₁ c₂ = record c₁ { preds = (preds c₁ ++ preds c₂); succs = (succs c₁ ++ succs c₂) }

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
    -- The id of the maximum node in the graph.
    sucMaxId : ∀ {n} → G n → ℕ
    -- Shrink the graph's max id to the smallest id in the graph.
    shrink : ∀ {n} (g : G n) → G (sucMaxId g)

  isEmpty : ∀ {n} → G n → Bool
  isEmpty g with matchAny g
  ...          | ∅ = true
  ...          | _ & _ = false
open Graph {{...}} public

-- Mapping functions for contexts and graphs. Particularly useful when
-- needing to move nodes and edges between graphs of different sizes.
-- f : a transformation on the upper bound of node ids
-- f-fin : a type-consistent transformation on the node ids themselves
module Maps (f : ℕ → ℕ) (f-fin : ∀ {n} → Fin n → Fin (f n)) where
  mapEdge : ∀ {n} → Edge × Fin n → Edge × Fin (f n)
  mapEdge p = Product.map Fn.id f-fin p
  mapContext : ∀ {n} {n-fin : Fin n} →
               (Edge × Fin n → Edge × Fin (f n)) →
               Context n-fin → Context (f-fin n-fin)
  mapContext {_} {n-fin} f-edge ctxt-n = ctxt-f
    where
    open Context ctxt-n
    ctxt-f : Context (f-fin n-fin)
    preds ctxt-f = List.map f-edge preds
    label ctxt-f = label
    succs ctxt-f = List.map f-edge succs

private
  -- Implements the Graph interface with AVL trees. Keeps contexts
  -- ordered by id, re-ordering insertions to maintain the invariant
  -- that the (internal) context for `id` only refers to nodes with
  -- smaller ids. This allows searches for edges relating to nodes
  -- with large ids to be fast (though better, more complicated
  -- representations certainly exist).
  module Impl where
    open import Data.Fin.Properties as FinP
    open import Relation.Binary using (StrictTotalOrder; IsStrictTotalOrder)
    import Data.AVL
    module FinOrd (n : ℕ) = StrictTotalOrder (FinP.strictTotalOrder n)
    module AVL (n : ℕ) = Data.AVL Context (FinOrd.isStrictTotalOrder n)

    module ImplMaps (f : ℕ → ℕ) (f-fin : ∀ {n} → Fin n → Fin (f n)) where
      open Maps f f-fin
      mapKV : ∀ {n} → AVL.KV n → AVL.KV (f n)
      mapKV kv = Product.map f-fin (mapContext mapEdge) kv
      mapTree : ∀ {n} → AVL.Tree n → AVL.Tree (f n)
      mapTree {n} t = t-f
        where
        l = AVL.toList n t
        l-f = List.map mapKV l
        t-f = AVL.fromList (f n) l-f

    instance
      AVLGraph : Graph AVL.Tree
      empty {{AVLGraph}} {n} = AVL.empty n
      insert {{AVLGraph}} {n} c g =
        AVL.insert (suc n) (fromℕ n) c (ImplMaps.mapTree suc Fin.inject₁ g)
      reinsert {{AVLGraph}} {n} {id} c g = AVL.insert n id c-clean g-augmented
        where
        module AVLn = AVL n
        open Context
        open IsStrictTotalOrder (FinOrd.isStrictTotalOrder n) using (_<?_)
        augmentingContexts : List AVLn.KV
        augmentingContexts = predCtxts ++ succCtxts
          where
          predEdgeToCtxt : Edge × Fin n → Maybe AVLn.KV
          predEdgeToCtxt (e , id-out) with ⌊ id <? id-out ⌋
          ... | true = just (id , context [] (label c) [ (e , id) ])
          ... | false = nothing
          succEdgeToCtxt : Edge × Fin n → Maybe AVLn.KV
          succEdgeToCtxt (e , id-out) with ⌊ id <? id-out ⌋
          ... | true = just (id , context [ (e , id) ] (label c) [])
          ... | false = nothing
          predCtxts = List.gfilter predEdgeToCtxt (preds c)
          succCtxts = List.gfilter succEdgeToCtxt (succs c)
        augmentContexts : AVLn.Tree → AVLn.KV → AVLn.Tree
        augmentContexts g (id , c) = updated
          where
          maybeC = AVLn.lookup id g
          update : ∀ {id'} → AVLn.Tree → Context id' → AVLn.Tree
          update {id'} g c = AVLn.insertWith id' c (Contexts.merge) g
          updated = Maybe.maybe′ (update g) g maybeC
        g-augmented : AVLn.Tree
        g-augmented = List.foldl augmentContexts g augmentingContexts
        c-clean : Context id
        c-clean = context (filter filtFn (preds c))
                          (label c)
                          (filter filtFn (succs c))
          where
          filtFn =  not ∘ ⌊_⌋ ∘ (_<?_ id) ∘ proj₂
      matchAny {{AVLGraph}} {n} g with AVL.initLast n g
      ...                            | nothing = ∅
      ...                            | just (g' , (_ , c)) = c & g'
      match {{AVLGraph}} {n} id g = matchImpl id g
        where
        module AVLn = AVL n
        open Context
        extractContext : (id : Fin n) → AVL.Tree n → Maybe (Context id)
        extractContext id g = mergedC
          where
            open IsStrictTotalOrder (FinOrd.isStrictTotalOrder n) using (_<?_)
            listG =  AVLn.toList g
            filteredG = List.takeWhile (⌊_⌋ ∘ (_<?_ id) ∘ proj₁) listG
            mergeContexts : {id₂ : Fin n} (c₁ : Context id) (c₂ : Context id₂)
                          → Context id
            mergeContexts c₁ c₂ = context preds-merged (label c₁) succs-merged
              where
              connectsC₁? : Edge × Fin n → Bool
              connectsC₁? = ⌊_⌋ ∘ (FinP._≟_ id) ∘ proj₂
              preds-merged = filter connectsC₁? (succs c₂) ++ (preds c₁)
              succs-merged = filter connectsC₁? (preds c₂) ++ (succs c₁)
            foldContexts : AVLn.KV → Context id → Context id
            foldContexts (id₂ , c₂) c₁ = mergeContexts c₁ c₂
            maybeC = AVLn.lookup id g
            mergedC = Maybe.map (λ c → List.foldr foldContexts c filteredG) maybeC

        removeContext : (id : Fin n) → AVL.Tree n → AVL.Tree n
        removeContext id g =  filteredG
          where
          removeId : AVLn.KV → Maybe AVLn.KV
          removeId (id₂ , c₂) with ⌊ id FinP.≟ id₂ ⌋
          ... | true = nothing
          ... | false = just (id₂ , context filtPreds (label c₂) filtSuccs)
            where
            filterContexts : Edge × Fin n → Bool
            filterContexts = ⌊_⌋ ∘ (FinP._≟_ id) ∘ proj₂
            filtPreds = filter filterContexts (preds c₂)
            filtSuccs = filter filterContexts (succs c₂)
          filteredG : AVLn.Tree
          filteredG = AVLn.fromList ∘ List.gfilter removeId $ AVLn.toList g

        matchImpl : Fin n → AVLn.Tree → Decomp AVL.Tree n
        matchImpl id g with extractContext id g
        ... | nothing = ∅
        ... | just c = c & removeContext id g
      sucMaxId {{AVLGraph}} g with matchAny g
      ... | ∅ = 0
      ... | _&_ {_} {id} _ _ = suc $ Fin.toℕ id
      -- WARNING: The below is implemented incorrectly.
      -- To implement the below, we need to construct a proof that sucMaxId
      -- is greater than all elements in the tree. AVL doesn't have any
      -- convenient functions to do this and this function isn't that important,
      -- so I'm just going to leave it unimplemented :(
      shrink {{AVLGraph}} {n} g = AVL.empty (sucMaxId g)
