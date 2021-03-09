import modal_logic.basic

namespace ontological_argument

open modal_logic

open_locale modal_frame.universal

constant object : Type

variables [world.{0}] (w : World) (p q : object → MProp)

constant ex (x : object) : MProp
constant pos : (object → MProp) → MProp
axiom pos_of_imp_of_pos : w ⊩ □(λ v, ∀ x, v ⊩ ex x ⇒ p x ⇒ q x) ⇒ pos p ⇒ pos q
axiom not_pos : w ⊩ ¬pos p ⇔ pos (not ∘ p)

lemma not_pos_eq_pos_not : (¬pos p) = pos (not ∘ p) :=
begin
  ext,
  apply not_pos,
end

theorem exists_of_pos : w ⊩ pos p ⇒ ◇(λ v, ∃ x, v ⊩ ex x ∧ p x) :=
begin
  intros h,
  rw ← modal_logic.not_not (◇_),
  intros h',
  simp only [not_lam, not_poss] at h',
  simp only [not_exists, not_sat, modal_logic.not_and, or_eq_not_imp_left, modal_logic.not_not] at h',
  have h'' := h,
  revert h'',
  show w ⊩ ¬pos p,
  rw not_pos_eq_pos_not,
  apply pos_of_imp_of_pos _ p _ _ h,
  intros v h_v x h_x h'',
  apply h' v h_v x h_x,
end

def godlike (g : object) : MProp := λ w, ∀ p, w ⊩ pos p ⇒ p g
axiom pos_godlike : w ⊩ pos godlike

theorem exists_godlike : w ⊩ ◇(λ v, ∃ x, v ⊩ ex x ∧ godlike x) :=
begin
  apply exists_of_pos,
  apply pos_godlike,
end

def ess (p : object → MProp) (x : object) : MProp := ex x ∧ p x ∧ (λ w, ∀ q : object → MProp, w ⊩ q x ⇒ □(λ v, ∀ y, v ⊩ ex y ⇒ p y ⇒ q y))
axiom nec_pos_of_pos : w ⊩ pos p ⇒ □pos p

lemma pos_of_godlike (x) : w ⊩ godlike x ⇒ p x ⇒ pos p :=
begin
  intros h h',
  by_contra h'',
  simp only [not_sat, not_pos_eq_pos_not] at h'',
  apply h _ h'' h',
end

theorem ess_godlike (x) : w ⊩ ex x ⇒ godlike x ⇒ ess godlike x :=
begin
  intros h h',
  split,
  {
    apply h,
  },
  split,
  {
    apply h',
  },
  {
    intros p h'' v h_v y h''' h'''',
    apply h'''',
    apply nec_pos_of_pos w _ _ v h_v,
    apply pos_of_godlike _ _ _ h' h'',
  },
end

def nec_ex (x : object) : MProp := λ w, ∀ p, w ⊩ ess p x ⇒ □(λ v, ∃ y, v ⊩ ex y ∧ p y)
axiom pos_nec_ex : w ⊩ pos nec_ex

lemma ex_of_godlike (x) : w ⊩ godlike x ⇒ ex x :=
begin
  intros h,
  rcases exists_godlike w with ⟨v, h_v, ⟨y, h', h''⟩⟩,
  apply h,
  apply nec_pos_of_pos v ex _ w trivial,
  apply pos_of_godlike _ _ _ h'' h',
end

theorem god_nec_ex : ∃ x, w ⊩ ex x ∧ godlike x :=
begin
  rcases exists_godlike w with ⟨v, h_v, x, h, h'⟩,
  apply h' _ (pos_nec_ex _) _ (ess_godlike _ _ h h') w trivial,
end

theorem modal_collapse (w v : World) : w = v :=
begin
  rcases god_nec_ex w with ⟨god_w, -, h⟩,
  rcases god_nec_ex v with ⟨god_v, -, h'⟩,
  apply h' (λ _ u, w = u),
  apply nec_pos_of_pos w _ _ v trivial,
  apply pos_of_godlike _ _ _ h,
  apply rfl,
end

end ontological_argument