import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Lemmas  -- For list utilities
open Std

namespace lang



variable {σ : Type}[DecidableEq σ]

variable (Alph : Finset σ)

def Word : Type
:= List Alph

def Lang : Type
:= Word Alph → Prop

end lang

open lang

abbrev Alph : Finset Char
:= {'a','b','c'}

instance (α : Sort _) (x : α) :
    Fact (x ∈ ({x} : Finset α)) :=
  by constructor; simp

instance (α : Sort _) [DecidableEq α] (x : α) (s : Finset α) :
    Fact (x ∈ insert x s) :=
  by constructor; simp

instance (α : Sort _) [DecidableEq α] (x y : α) (s : Finset α) [Fact (x ∈ s)] :
    Fact (x ∈ insert y s) := by
  constructor
  rw [Finset.mem_insert]
  exact Or.inr (Fact.elim inferInstance)

@[match_pattern]
abbrev Finset.ofFactMem {α : Sort _} (x : α) (s : Finset α) [Fact (x ∈ s)] : s :=
  ⟨x, Fact.elim inferInstance⟩

@[match_pattern]
abbrev Finset.ofFactMem' {α : Sort _} (x : α) {s : Finset α} [Fact (x ∈ s)] : s :=
  Finset.ofFactMem x s

instance : Coe String (List Char) where
  coe s := s.data

prefix:max "~" => Finset.ofFactMem'

def w1 : Word Alph
  := [~'a',~'b',~'c']

instance (α : Sort _)(Alph : Finset α) :
    Fact ((x : α) → (x ∈ []) → (x ∈ Alph)) :=
  by constructor; simp

instance (α : Sort _)(Alph : Finset α)(y : α)(ys : List α)
  [Fact (y ∈ Alph)][Fact ((x : α) → (x ∈ ys) → (x ∈ Alph)) ] :
   Fact ((x : α) → (x ∈ y :: ys) → (x ∈ Alph)) :=
  by simp_all [fact_iff]

@[match_pattern]
abbrev Finset.ListofFactMem {α : Sort _} (ys : List α) (Alph : Finset α)
    [inst : Fact ((x : α) → (x ∈ ys) → (x ∈ Alph)) ] : Word Alph :=
  ys.attach.map (λ x : {x // x ∈ ys} ↦ letI : Fact (x.val ∈ Alph) := ⟨inst.elim x.val x.prop⟩ ; ~ x.val)

@[match_pattern]
abbrev Finset.ListofFactMem' {α : Sort _} (ys : List α) {Alph : Finset α}
    [inst : Fact ((x : α) → (x ∈ ys) → (x ∈ Alph)) ] : Word Alph :=
  ys.attach.map (λ x : {x // x ∈ ys} ↦ letI : Fact (x.val ∈ Alph) := ⟨inst.elim x.val x.prop⟩ ; ~ x.val)

prefix:max "~~" => Finset.ListofFactMem'

def w2 : Word Alph
  := ~~ ['a','b','c']

--prefix:max "~~~" => Finset.ListofFactMem' ∘ String.data

def w3 : Word Alph
  := ~~ "abc"

/-
def w4 : Word Alph
  := ~~ "abd"
-/
def l1 : Lang Alph
:= λ w ↦ w = ~~ "abc"

example : l1 (~~ "abc")
:= by dsimp [l1]

instance : Coe (Finset (Word Alph)) (Lang Alph) where
  coe s := λ x ↦ x ∈ s

def l2_aux : Finset (Word Alph)
:= { ~~ "abc"}

def l2 : Lang Alph
:= l2_aux

/-
def l3 : Lang Alph
:= { (~~ "abc") }
-/

def l4 : Lang Alph
:= ({ (~~ "abc" : Word Alph) } : Finset (Word Alph))
