import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod

@[simp] def Finset.map' [DecidableEq β] (s : Finset α) (f : α → β) :=
  (s.val.map f).toFinset



variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

class FinSupp (f : α → Nat) where
  supp : Finset α
  mem_iff : ∀ x, x ∈ supp ↔ f x > 0

def supp (f : α → Nat) [h : FinSupp f] := h.supp
theorem supp_mem_iff (f : α → Nat) [h : FinSupp f] :
  x ∈ supp f ↔ f x > 0 := h.mem_iff x
theorem supp_not_mem_iff (f : α → Nat) [h : FinSupp f] :
  x ∉ supp f ↔ f x = 0 := by simp [supp_mem_iff f]

variable {f g : α → Nat}

instance : FinSupp (λ _ : α => 0) where
  supp := ∅
  mem_iff := by intro; simp

instance [FinSupp f] [FinSupp g] : FinSupp (λ x => f x + g x) where
  supp := supp f ∪ supp g
  mem_iff := by
    intro x
    simp [supp_mem_iff f, supp_mem_iff g]

instance [FinSupp f] : FinSupp (λ x => f x * g x) where
  supp := (supp f).filter (λ x => g x ≠ 0)
  mem_iff := by
    intro x
    simp [supp_mem_iff f, ←Nat.pos_iff_ne_zero]

instance [FinSupp g] : FinSupp (λ x => f x * g x) := by
  simp [λ x => Nat.mul_comm (f x) (g x)]
  exact inferInstance

theorem supp_unique (h₁ : FinSupp f) (h₂ : FinSupp f) :
  h₁.supp = h₂.supp := by
  ext x
  simp [h₁.mem_iff, h₂.mem_iff]

theorem FinSupp.unique (h₁ : FinSupp f) (h₂ : FinSupp f) : h₁ = h₂ := by
  have h := supp_unique h₁ h₂
  cases h₁; cases h₂; congr

def FinSupp.of_mem_if (s : Finset α) (h : ∀ x, f x > 0 → x ∈ s) :
  FinSupp f where
  supp := s.filter (λ x => f x > 0)
  mem_iff := by
    intro x
    simp
    apply h



def Multiset.sumBy (s : Multiset α) (f : α → Nat) :=
  (s.map f).sum

namespace Multiset

variable {s t : Multiset α}

theorem sum_by_ext (h : ∀ x ∈ s, f x = g x) : s.sumBy f = s.sumBy g := by
  simp [sumBy]
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    simp [h]
    apply ih
    intro x h₁
    apply h
    simp [h₁]

theorem sum_by_zero : s.sumBy (λ _ => 0) = 0 := by
  simp [sumBy]

theorem sum_by_zero' (h : ∀ x ∈ s, f x = 0) : s.sumBy f = 0 := by
  rw [←sum_by_zero]
  exact sum_by_ext h

theorem sum_by_le (h : ∀ x ∈ s, f x ≤ g x) : s.sumBy f ≤ s.sumBy g := by
  simp [sumBy]
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    simp [h]
    apply Nat.add_le_add
    · apply h; simp
    · apply ih; intro x h₁; apply h; simp [h₁]

theorem sum_by_add :
  s.sumBy (λ x => f x + g x) = s.sumBy f + s.sumBy g := by
  simp [sumBy]

theorem sum_by_nmul :
  s.sumBy (λ x => a * f x) = a * s.sumBy f := by
  simp [sumBy]
  exact sum_map_nsmul

theorem add_sum_by :
  (s + t).sumBy f = s.sumBy f + t.sumBy f := by
  simp [sumBy]

theorem le_sum_by :
  s ≤ t → s.sumBy f ≤ t.sumBy f := by
  intro h
  rw [←eq_union_left h]
  simp [union_def, add_sum_by]

theorem sprod_sum_by {s : Multiset α} {t : Multiset β} {f : α → β → Nat} :
  s.sumBy (λ x => t.sumBy (f x ·)) = (s ×ˢ t).sumBy f.uncurry := by
  simp [sumBy]
  induction s using Multiset.induction_on with
  | empty => simp
  | cons ih => simp [←ih]

theorem swap_sum_by {s : Multiset α} {t : Multiset β} {f : α → β → Nat} :
  s.sumBy (λ x => t.sumBy (f x ·)) = t.sumBy (λ y => s.sumBy (f · y)) := by
  simp [sumBy]
  induction s using Multiset.induction_on with
  | empty => simp
  | cons ih => simp [ih]

end Multiset



def usum (f : α → Nat) [FinSupp f] :=
  (supp f).val.sumBy f
notation3 "∑" (...) ", " s:(scoped f => usum f) => s

lemma usum_supp (s : Finset α) (f : α → Nat) [FinSupp f]
  (h : ∀ x, f x > 0 → x ∈ s) : (∑ x, f x) = s.val.sumBy f := by
  simp [usum]
  have h₁ : supp f ⊆ s := by
    intro x h₁
    simp [supp_mem_iff f] at h₁
    apply h at h₁
    exact h₁
  rw [←Multiset.eq_union_left (Finset.val_le_iff.mpr h₁)]
  simp [Multiset.union_def, Multiset.add_sum_by]
  apply Multiset.sum_by_zero'
  intro x h₂
  rw [←Finset.sdiff_val, Finset.mem_val] at h₂
  simp at h₂
  rcases h₂ with ⟨_, h₂⟩
  simp [supp_not_mem_iff] at h₂
  exact h₂

theorem usum_ext [FinSupp f] [FinSupp g]
  (h : ∀ x, f x = g x) : (∑ x, f x) = (∑ x, g x) := by
  let s := supp f ∪ supp g
  rw [usum_supp s f, usum_supp s g]
  · apply Multiset.sum_by_ext
    simp [h]
  all_goals simp [supp_mem_iff]; tauto

theorem usum_le [FinSupp f] [FinSupp g]
  (h : ∀ x, f x ≤ g x) : (∑ x, f x) ≤ (∑ x, g x) := by
  let s := supp f ∪ supp g
  rw [usum_supp s f, usum_supp s g]
  · apply Multiset.sum_by_le
    simp [h]
  all_goals simp [supp_mem_iff]; tauto

theorem usum_zero : (∑ _ : α, 0) = 0 := Multiset.sum_by_zero

theorem usum_zero_iff [FinSupp f] : (∑ x, f x) = 0 ↔ ∀ x, f x = 0 := by
  constructor
  · intro h₁ x
    simp [usum] at h₁
    by_contra h₂
    simp [←Nat.pos_iff_ne_zero] at h₂
    let s : Multiset α := {x}
    have h₃ : s ≤ (supp f).val := by
      simp [supp_mem_iff]; exact h₂
    apply Multiset.le_sum_by (f := f) at h₃
    rw [h₁] at h₃
    simp [Multiset.sumBy] at h₃
    rw [h₃] at h₂
    contradiction
  · intro h
    apply Multiset.sum_by_zero'
    intro x _
    simp [h]

theorem usum_pos_iff [FinSupp f] : (∑ x, f x) > 0 ↔ ∃ x, f x > 0 := by
  constructor <;> intro h₁ <;> by_contra h₂ <;> simp at h₂
  · rw [←usum_zero_iff] at h₂
    rw [h₂] at h₁
    contradiction
  · rw [usum_zero_iff] at h₂
    rcases h₁ with ⟨x, h₁⟩
    rw [h₂ x] at h₁
    contradiction

theorem usum_add [FinSupp f] [FinSupp g] :
  (∑ x, f x + g x) = (∑ x, f x) + (∑ x, g x) := by
  conv => lhs; simp [usum, Multiset.sum_by_add]
  apply congr_arg₂ <;> symm <;> apply usum_supp
    <;> intro x h <;> simp [supp_mem_iff, h]

theorem usum_nmul [FinSupp f] :
  (∑ x, a * f x) = a * (∑ x, f x) := by
  by_cases h : a = 0
  · simp [h]
    apply Multiset.sum_by_zero'
    simp [h]
  · simp [←Nat.pos_iff_ne_zero] at h
    conv => lhs; simp [usum, Multiset.sum_by_nmul]
    apply congr_arg
    symm
    apply usum_supp
    intro x h₁
    simp [supp_mem_iff, h₁]
    exact h



abbrev FinSupp₂ (f : α → β → Nat) := FinSupp f.uncurry
abbrev supp₂ (f : α → β → Nat) [FinSupp₂ f] := supp f.uncurry

variable {f : α → β → Nat}

-- instance [h : FinSupp f.uncurry] : FinSupp₂ f := h

instance [FinSupp₂ f] : FinSupp (f x ·) :=
  FinSupp.of_mem_if
    ((supp₂ f).map' Prod.snd)
    (by intro y h; simp [supp_mem_iff]; exists x)

instance [FinSupp₂ f] : FinSupp (f · y) :=
  FinSupp.of_mem_if
    ((supp₂ f).map' Prod.fst)
    (by intro x h; simp [supp_mem_iff]; exists y)

instance [FinSupp₂ f] : FinSupp (λ x => ∑ y, f x y) :=
  FinSupp.of_mem_if
    ((supp₂ f).map' Prod.fst)
    (by intro x; simp [usum_pos_iff, supp_mem_iff]; intro y h; exists y)

instance [FinSupp₂ f] : FinSupp (λ y => ∑ x, f x y) :=
  FinSupp.of_mem_if
    ((supp₂ f).map' Prod.snd)
    (by intro y; simp [usum_pos_iff, supp_mem_iff]; intro x h; exists x)

theorem usum_swap [FinSupp₂ f] :
  (∑ x, ∑ y, f x y) = (∑ y, ∑ x, f x y) := by
  let s := (supp₂ f).map' Prod.fst
  let t := (supp₂ f).map' Prod.snd
  have h₁ : (∑ x, ∑ y, f x y) =
    s.val.sumBy (λ x => t.val.sumBy (λ y => f x y)) := by
    rw [usum_supp]
    · congr; funext x
      rw [usum_supp]
      intro y _; simp [supp_mem_iff]; exists x
    · intro x; simp [usum_pos_iff, supp_mem_iff]; intro y _; exists y
  have h₂ : (∑ y, ∑ x, f x y) =
    t.val.sumBy (λ y => s.val.sumBy (λ x => f x y)) := by
    rw [usum_supp]
    · congr; funext x
      rw [usum_supp]
      intro y _; simp [supp_mem_iff]; exists x
    · intro x; simp [usum_pos_iff, supp_mem_iff]; intro y _; exists y
  rw [h₁, h₂, Multiset.swap_sum_by]



structure Bag (α : Type u) where
  f : α → Nat
  [finSupp : FinSupp f]

instance : CoeFun (Bag α) (λ _ => α → Nat) := ⟨Bag.f⟩
instance {b : Bag α} : FinSupp b := b.finSupp

instance : EmptyCollection (Bag α) := ⟨{ f := λ _ => 0 }⟩

instance : Singleton α (Bag α) := ⟨λ a => {
  f := λ x => if x = a then 1 else 0
  finSupp := {
    supp := {a}
    mem_iff := by
      intro x
      by_cases h : x = a <;> simp [h, supp_mem_iff]
  }
}⟩

instance : Insert α (Bag α) := ⟨λ a b => {
  f := λ x => if x = a then b x + 1 else b x
  finSupp := {
    supp := insert a (supp b)
    mem_iff := by
      intro x
      by_cases h : x = a <;> simp [h, supp_mem_iff]
  }
}⟩

instance : Add (Bag α) := ⟨λ b₁ b₂ => { f := λ x => b₁ x + b₂ x }⟩
instance : SProd (Bag α) (Bag β) (Bag (α × β)) := ⟨λ b₁ b₂ => {
  f := λ (x, y) => b₁ x * b₂ y
  finSupp := FinSupp.of_mem_if
    (supp b₁ ×ˢ supp b₂)
    (by intro ⟨x, y⟩; simp [supp_mem_iff])
}⟩

def Bag.dedup (b : Bag α) : Bag α where
  f := λ x => if b x > 0 then 1 else 0
  finSupp := {
    supp := supp b
    mem_iff := by
      intro x
      by_cases h : b x > 0 <;> simp [h, supp_mem_iff]
  }

def Bag.filter (b : Bag α) (p : α → Bool) : Bag α where
  f := λ x => b x * if p x then 1 else 0

def Bag.map (b : Bag α) (f : α → β) : Bag β where
  f := λ y => ∑ x, b x * if f x = y then 1 else 0
  finSupp := {
    supp := (supp b).map' f
    mem_iff := by
      intro y
      simp [supp_mem_iff, usum_pos_iff]
      apply exists_congr
      intro x
      by_cases h : f x = y <;> simp [h]
  }
