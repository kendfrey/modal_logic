import modal_logic.classes

class is_dense (α : Type*) (r : α → α → Prop) : Prop :=
(dense : ∀ a b, r a b → ∃ c, r a c ∧ r c b)

instance is_refl.is_dense {α r} [is_refl α r] : is_dense α r := ⟨λ a b h, ⟨a, refl a, h⟩⟩

class is_serial (α : Type*) (r : α → α → Prop) : Prop :=
(serial : ∀ a, ∃ b, r a b)

instance is_refl.is_serial {α r} [is_refl α r] : is_serial α r := ⟨λ a, ⟨a, refl a⟩⟩

class is_euclidean (α : Type*) (r : α → α → Prop) : Prop :=
(euc : ∀ a b c, r a b → r a c → r b c)

instance is_per.is_euclidean {α r} [is_per α r] : is_euclidean α r := ⟨λ a b c h h', trans (symm h) h'⟩

class is_semieuclidean (α : Type*) (r : α → α → Prop) :=
(semieuc : ∀ a b c, r a b → r a c → r b c ∨ r c b)

instance is_euclidean.is_semieuclidean {α r} [is_euclidean α r] : is_semieuclidean α r := ⟨λ a b c h h', or.inl (is_euclidean.euc a b c h h')⟩

class is_founded (α : Type*) (r : α → α → Prop) : Prop :=
(founded : ∀ a, ∃ b, r a b ∧ ∀ c, r b c → b = c)

class is_convergent (α : Type*) (r : α → α → Prop) : Prop :=
(conv : ∀ a b c, r a b → r a c → ∃ d, r b d ∧ r c d)

class is_discrete (α : Type*) (r : α → α → Prop) : Prop :=
(disc : ∀ a b, r a b → a = b)

class is_functional (α : Type*) (r : α → α → Prop) : Prop :=
(func : ∀ a b c, r a b → r a c → b = c)

class is_function (α : Type*) (r : α → α → Prop) extends is_serial α r, is_functional α r : Prop

instance is_discrete.is_functional {α r} [is_discrete α r] : is_functional α r := ⟨λ a b c h h', eq.trans (is_discrete.disc a b h).symm (is_discrete.disc a c h')⟩

class is_right_refl (α : Type*) (r : α → α → Prop) : Prop :=
(refl : ∀ a b, r a b → r b b)

instance is_refl.is_right_refl {α r} [is_refl α r] : is_right_refl α r := ⟨λ a b h, refl b⟩

namespace modal_logic

variables [_modal_model : modal_frame] (w : World) (p q : MProp)

lemma em : w ⊩ p ∨ ¬p := em _

@[simp] lemma not_sat : (¬(w ⊩ p)) = (w ⊩ ¬p) := rfl

lemma not_lam : (¬(λ w, p w)) = (λ w, ¬p w) := rfl

@[simp] lemma not_not : (¬¬p) = p :=
  by ext; simp only [not, iff, sat, not_not]

@[simp] lemma not_imp : (¬(p ⇒ q)) = (p ∧ ¬q) :=
  by ext; simp only [not, imp, and, iff, sat, not_imp]

@[simp] lemma not_and : (¬(p ∧ q)) = (¬p ∨ ¬q) :=
  by ext; simp only [not, and, or, iff, sat, not_and_distrib]

@[simp] lemma not_or : (¬(p ∨ q)) = (¬p ∧ ¬q) :=
  by ext; simp only [not, and, or, iff, sat, not_or_distrib]

@[simp] lemma not_poss : (¬◇p) = □¬p :=
  by ext; simp only [not, nec, poss, iff, sat, not_exists, _root_.not_and]

@[simp] lemma not_nec : (¬□p) = ◇¬p :=
  by ext; simp only [not, nec, poss, iff, sat, not_forall, exists_prop]

@[simp] lemma nec_and : □(p ∧ q) = (□p ∧ □q) :=
  by ext; simp only [nec, and, iff, sat, forall_and_distrib]

@[simp] lemma poss_or : ◇(p ∨ q) = (◇p ∨ ◇q) :=
  by ext; simp only [poss, or, iff, sat, ← exists_prop, exists_or_distrib]

lemma and_comm : (p ∧ q) = (q ∧ p) :=
  by ext; simp only [and, iff, sat, and_comm]

lemma or_comm : (p ∨ q) = (q ∨ p) :=
  by ext; simp only [or, iff, sat, or_comm]

lemma or_eq_not_imp_left : (p ∨ q) = (¬p ⇒ q) :=
  by ext; simp only [imp, not, or, iff, sat, or_iff_not_imp_left]

lemma or_eq_not_imp_right : (p ∨ q) = (¬q ⇒ p) :=
  by ext; simp only [imp, not, or, iff, sat, or_iff_not_imp_right]

lemma nec_imp_nec_of_nec_imp : w ⊩ □(p ⇒ q) ⇒ □p ⇒ □q :=
  λ h h' v h_v, h v h_v (h' v h_v)

lemma of_nec [is_refl World (≺)] : w ⊩ □p ⇒ p :=
  λ h, h w (refl w)

lemma nec_nec_of_nec [is_trans World (≺)] : w ⊩ □p ⇒ □□p :=
  λ h v h_v u h_u, h u (trans h_v h_u)

lemma nec_of_nec_nec [is_dense World (≺)] : w ⊩ □□p ⇒ □p :=
  λ h v h_v, let ⟨u, h_u, h_u'⟩ := is_dense.dense w v h_v in h u h_u v h_u'

lemma poss_of_nec [is_serial World (≺)] : w ⊩ □p ⇒ ◇p :=
  λ h, let ⟨v, h_v⟩ := is_serial.serial w in ⟨v, h_v, h v h_v⟩

lemma nec_poss [is_symm World (≺)] : w ⊩ p ⇒ □◇p :=
  λ h v h_v, ⟨w, symm h_v, h⟩

lemma nec_poss_of_poss [is_euclidean World (≺)] : w ⊩ ◇p ⇒ □◇p :=
  λ ⟨u, h_u, h⟩ v h_v, ⟨u, is_euclidean.euc w v u h_v h_u, h⟩

lemma nec_of_nec_nec_imp [is_trans World (≺)] (wf : well_founded (λ w v : World, v ≺ w)) : w ⊩ □(□p ⇒ p) ⇒ □p :=
  by apply well_founded.induction wf w; exact λ v ih h u h_u, h u h_u (ih u h_u (λ t h_t, h t (trans h_u h_t)))

lemma of_nec_nec_imp_nec_imp [is_preorder World (≺)] (wf : well_founded (λ w v : World, w ≠ v ∧ v ≺ w)) : w ⊩ □(□(p ⇒ □p) ⇒ p) ⇒ p :=
begin
  have : is_antisymm World (≺),
  {
    constructor,
    intros v u h_u h_v,
    rcases well_founded.has_min wf {v, u} ⟨v, set.mem_insert _ _⟩ with ⟨t, h_t, h⟩,
    simp only [set.mem_insert_iff, set.mem_singleton_iff, _root_.not_and, not_imp_not] at h h_t,
    rcases h_t with rfl | rfl,
    {
      exact (h u (or.inr rfl) h_u).symm,
    },
    {
      exact h v (or.inl rfl) h_v,
    },
  },
  intros h,
  by_contra h_w_p,
  obtain ⟨v, h_v, h_v_p, h'⟩ : ∃ v, w ≺ v ∧ ¬(v ⊩ p) ∧ ∀ u, u ≠ v → v ≺ u → u ⊩ p,
  {
    rcases well_founded.has_min wf { v | w ≺ v ∧ ¬(v ⊩ p) } ⟨w, refl w, h_w_p⟩ with ⟨v, ⟨h_v, h_v'⟩, h'⟩,
    simp only [set.mem_set_of_eq, and_imp, not_imp_not] at h',
    exact ⟨v, h_v, h_v', λ u h_u h_u', h' u (trans h_v h_u') h_u h_u'⟩,
  },
  refine h_v_p (h v h_v _),
  intros u h_u h_u_p t h_t,
  by_cases h'' : u = t,
  {
    exact h'' ▸ h_u_p,
  },
  {
    exactI h' t (λ h''', (h'' (antisymm h_t (h'''.symm ▸ h_u)))) (trans h_u h_t),
  },
end

lemma nec_nec_imp_or_nec_nec_imp [is_semieuclidean World (≺)] : w ⊩ □(□p ⇒ q) ∨ □(□q ⇒ p) :=
begin
  simp only [or_eq_not_imp_left, not_imp, not_nec],
  rintros ⟨v, h_v, h, h'⟩ u h_u h'',
  rcases is_semieuclidean.semieuc w v u h_v h_u with h_u' | h_v',
  {
    exact h u h_u',
  },
  {
    exact false.rec _ (h' (h'' v h_v')),
  },
end

lemma poss_nec_of_nec_poss [is_trans World (≺)] [is_founded World (≺)] : w ⊩ □◇p ⇒ ◇□p :=
  λ h, let ⟨v, h_v, h_v'⟩ := is_founded.founded w in ⟨v, h_v, λ u h_u, let ⟨t, h_t, h'⟩ := h v h_v in h_v' u h_u ▸ (h_v' t h_t).symm ▸ h'⟩

lemma nec_poss_of_poss_nec [is_convergent World (≺)] : w ⊩ ◇□p ⇒ □◇p :=
  λ ⟨u, h_u, h⟩ v h_v, let ⟨t, h_t, h_t'⟩ := is_convergent.conv w v u h_v h_u in ⟨t, h_t, h t h_t'⟩

lemma nec_of [is_discrete World (≺)] : w ⊩ p ⇒ □p :=
  λ h u h_u, is_discrete.disc w u h_u ▸ h

lemma nec_of_poss [is_functional World (≺)] : w ⊩ ◇p ⇒ □p :=
  λ ⟨v, h_v, h⟩ u h_u, is_functional.func w v u h_v h_u ▸ h

lemma nec_eq_poss [is_function World (≺)] : ◇p = □p :=
  by ext; exact ⟨nec_of_poss w p, poss_of_nec w p⟩

lemma nec_nec_imp [is_right_refl World (≺)] : w ⊩ □(□p ⇒ p) :=
  λ v h_v h, h v (is_right_refl.refl w v h_v)

end modal_logic