import HTPILib.Chap3
namespace HTPI.Exercises

/- Sections 3.1 and 3.2 -/
-- 1.
theorem Exercise_3_2_1a (P Q R : Prop)
    (h1 : P → Q) (h2 : Q → R) : P → R := by
  assume hp
  show R from h2 (h1 hp)
  done

-- 2.
theorem Exercise_3_2_1b (P Q R : Prop)
    (h1 : ¬R → (P → ¬Q)) : P → (Q → R) := by
  assume hp
  assume hq
  by_contra contra
  apply h1 at contra
  apply contra at hp
  show False from hp hq
  done

-- 3.
theorem Exercise_3_2_2a (P Q R : Prop)
    (h1 : P → Q) (h2 : R → ¬Q) : P → ¬R := by
  assume hp
  apply h1 at hp
  by_contra hr
  apply h2 at hr
  show False from hr hp
  done

-- 4.
theorem Exercise_3_2_2b (P Q : Prop)
    (h1 : P) : Q → ¬(Q → ¬P) := by
  assume hq
  by_contra h2
  apply h2 at hq
  show False from hq h1
  done

/- Section 3.3 -/
-- 1.
theorem Exercise_3_3_1
    (U : Type) (P Q : Pred U) (h1 : ∃ (x : U), P x → Q x) :
    (∀ (x : U), P x) → ∃ (x : U), Q x := by
  assume H
  obtain (u: U) (h2: P u → Q u) from h1
  have h3: P u := H u
  exists u
  apply h2 h3
  done

-- 2.
theorem Exercise_3_3_8 (U : Type) (F : Set (Set U)) (A : Set U)
    (h1 : A ∈ F) : A ⊆ ⋃₀ F := by
  define -- subset
  fix a: U
  assume h: a ∈ A
  define -- union F
  exists A
  done

-- 3.
theorem Exercise_3_3_9 (U : Type) (F : Set (Set U)) (A : Set U)
    (h1 : A ∈ F) : ⋂₀ F ⊆ A := by
  define -- subset
  fix a: U
  assume h
  define at h -- intersection
  apply h at h1
  exact h1
  done

-- 4.
theorem Exercise_3_3_10 (U : Type) (B : Set U) (F : Set (Set U))
    (h1 : ∀ (A : Set U), A ∈ F → B ⊆ A) : B ⊆ ⋂₀ F := by
  define --subset
  fix a: U
  assume h
  define --intersection
  fix t: Set U
  assume ht
  apply h1 at ht
  apply ht
  exact h
  done

-- 5.
theorem Exercise_3_3_13 (U : Type)
    (F G : Set (Set U)) : F ⊆ G → ⋂₀ G ⊆ ⋂₀ F := by
  assume h
  define at h -- subset
  define -- subset
  fix a: U
  assume hg
  define at hg --intersection
  define -- intersection
  fix t: Set U
  assume ht
  apply hg
  apply h
  exact ht
  done

/- Section 3.4 -/
-- 1.
theorem Exercise_3_4_2 (U : Type) (A B C : Set U)
    (h1 : A ⊆ B) (h2 : A ⊆ C) : A ⊆ B ∩ C := by
  define --subset
  fix a: U
  assume ha
  define --and
  apply And.intro
  · -- a ∈ B
    define at h1 --subset
    apply h1
    exact ha
  · -- a ∈ C
    define at h2 --subset
    apply h2
    exact ha
  done

-- 2.
theorem Exercise_3_4_4 (U : Type) (A B C : Set U)
    (h1 : A ⊆ B) (h2 : A ⊈ C) : B ⊈ C := by
  by_contra h
  define at h1  --subset
  define at h   --subset
  define at h2  --subset
  contradict h2
  fix x : U
  assume ha
  apply h
  apply h1
  exact ha
  done

-- 3.
theorem Exercise_3_3_12 (U : Type)
    (F G : Set (Set U)) : F ⊆ G → ⋃₀ F ⊆ ⋃₀ G := by
  assume h
  define at h --subset
  define --subset
  fix a : U
  assume hf
  define --union
  define at hf --union
  obtain t h1 from hf
  exists t
  have h2: t ∈ G := h h1.left
  apply And.intro
  · exact h2
  · exact h1.right
  done

-- 4.
theorem Exercise_3_3_16 (U : Type) (B : Set U)
    (F : Set (Set U)) : F ⊆ 𝒫 B → ⋃₀ F ⊆ B := by
  assume h
  define at h --subset
  define --subset
  fix a : U
  assume hf
  define at hf --union
  obtain t ht from hf
  have ha: t ∈ 𝒫 B := h ht.left
  define at ha --power set
  apply ha
  exact ht.right
  done

-- 5.
theorem Exercise_3_3_17 (U : Type) (F G : Set (Set U))
    (h1 : ∀ (A : Set U), A ∈ F → ∀ (B : Set U), B ∈ G → A ⊆ B) :
    ⋃₀ F ⊆ ⋂₀ G := by
  define --subset
  fix a : U
  assume hf
  define at hf --union
  obtain A hA from hf
  define --intersection
  fix B : Set U
  assume hB
  have hAB: A ⊆ B := h1 A hA.left B hB
  define at hAB --subset
  apply hAB
  exact hA.right
  done

-- 6.
theorem Exercise_3_4_7 (U : Type) (A B : Set U) :
    𝒫 (A ∩ B) = 𝒫 A ∩ 𝒫 B := by
  apply Set.ext
  fix x
  apply Iff.intro
  · -- ->
    assume h
    define at h
    define -- and
    apply And.intro
    · -- ->
      define --power set
      fix a
      assume hx
      apply h at hx
      define at hx
      exact hx.left
    · -- <-
      define --power set
      fix a
      assume hx
      apply h at hx
      define at hx
      exact hx.right
  · --<-
    assume h
    define at h -- intersection
    have h1 := h.left
    define at h1 --power set
    have h2 := h.right
    define at h2 --power set
    define --power set
    fix a
    assume hx
    define --and
    apply And.intro
    · apply h1
      exact hx
    · apply h2
      exact hx
  done

-- 7.
theorem Exercise_3_4_17 (U : Type) (A : Set U) : A = ⋃₀ (𝒫 A) := by
  apply Set.ext
  fix x
  apply Iff.intro
  assume hx
  · define
    exists A
    apply And.intro
    · define
      fix a
      assume ha
      exact ha
    · exact hx
  · assume h
    define at h
    obtain X hX from h
    have h1 := hX.left
    define at h1
    have h2 := hX.right
    apply h1 at h2
    exact h2
  done

-- 8.
theorem Exercise_3_4_18a (U : Type) (F G : Set (Set U)) :
    ⋃₀ (F ∩ G) ⊆ (⋃₀ F) ∩ (⋃₀ G) := by
  define --subset
  fix a
  assume h
  define at h
  obtain X hX from h
  have h1 := hX.left
  define at h1
  define
  apply And.intro
  · define --union
    exists X
    apply And.intro
    · exact h1.left
    · exact hX.right
  · define --power set
    exists X
    apply And.intro
    · apply h1.right
    · apply hX.right
  done

-- 9.
theorem Exercise_3_4_19 (U : Type) (F G : Set (Set U)) :
    (⋃₀ F) ∩ (⋃₀ G) ⊆ ⋃₀ (F ∩ G) ↔
      ∀ (A B : Set U), A ∈ F → B ∈ G → A ∩ B ⊆ ⋃₀ (F ∩ G) := by
  apply Iff.intro
  · assume h
    define at h
    fix A
    fix B
    assume hA
    assume hB
    define --subset
    fix a
    assume ha
    define at ha
    apply h
    define --and
    apply And.intro
    · define --power set
      exists A
      apply And.intro hA ha.left
    · define --power set
      exists B
      apply And.intro hB ha.right
  · assume h
    define; fix a;
    assume h1; define at h1;
    have h2 := h1.left; define at h2; obtain A hA from h2
    have h3 := h1.right; define at h3; obtain B hB from h3
    have h4 := h A B hA.left hB.left
    define at h4
    apply h4
    define --and
    apply And.intro hA.right hB.right
  done

/- Section 3.5 -/
-- 1.
theorem Exercise_3_5_2 (U : Type) (A B C : Set U) :
    (A ∪ B) \ C ⊆ A ∪ (B \ C) := by
  define -- subset
  fix a
  assume h
  define at h
  have h1 := h.left; define at h1
  have h2 := h.right
  by_cases on h1
  · define --or
    apply Or.inl
    exact h1
  · define --or
    apply Or.inr
    define
    apply And.intro h1 h2
  done

-- 2.
theorem Exercise_3_5_5 (U : Type) (A B C : Set U)
    (h1 : A ∩ C ⊆ B ∩ C) (h2 : A ∪ C ⊆ B ∪ C) : A ⊆ B := by
  define at h1
  define at h2
  define; fix a; assume ha
  have h: a ∈ A ∪ C := Or.inl ha
  apply h2 at h; define at h
  by_cases on h
  · apply h
  · have h3: a ∈ A ∩ C := by
      define; apply And.intro ha h
    apply h1 at h3
    define at h3
    apply h3.left
  done

-- 3.
theorem Exercise_3_5_7 (U : Type) (A B C : Set U) :
    A ∪ C ⊆ B ∪ C ↔ A \ C ⊆ B \ C := by
  apply Iff.intro
  · -- ->
    assume h; define at h
    define; fix a; assume ha; define at ha
    have h1: a ∈ A ∪ C := by define; apply Or.inl ha.left
    apply h at h1; define at h1
    disj_syll h1 ha.right
    define; apply And.intro h1 ha.right
  · -- <-
    assume h; define at h
    define; fix a; assume ha; define at ha
    or_left with h1
    disj_syll ha h1
    have h2: a ∈ A \ C := by define; apply And.intro ha h1
    apply h at h2; define at h2
    apply h2.left
  done

-- 4.
theorem Exercise_3_5_8 (U : Type) (A B : Set U) :
    𝒫 A ∪ 𝒫 B ⊆ 𝒫 (A ∪ B) := by
  define; fix X
  assume h1; define at h1
  define; fix a; assume h2
  by_cases on h1
  · define at h1
    apply h1 at h2
    define; apply Or.inl h2
  · define at h1
    apply h1 at h2
    define; apply Or.inr h2
  done

-- 5.
theorem Exercise_3_5_17b (U : Type) (F : Set (Set U)) (B : Set U) :
    B ∪ (⋂₀ F) = {x : U | ∀ (A : Set U), A ∈ F → x ∈ B ∪ A} := by
  apply Set.ext; fix x
  apply Iff.intro
  · -- ->
    assume h1; define at h1
    define; fix A; assume h2
    by_cases on h1
    · apply Or.inl h1
    · define at h1; apply h1 at h2; apply Or.inr h2
  · -- <-
    assume h1; define at h1
    or_right with h2
    define; fix X; assume h3
    apply h1 at h3; define at h3
    disj_syll h3 h2; apply h3
  done

-- 6.
theorem Exercise_3_5_18 (U : Type) (F G H : Set (Set U))
    (h1 : ∀ (A : Set U), A ∈ F → ∀ (B : Set U), B ∈ G → A ∪ B ∈ H) :
    ⋂₀ H ⊆ (⋂₀ F) ∪ (⋂₀ G) := by
  define; fix a; assume h2; define at h2
  define; or_left with h3; define at h3; quant_neg at h3
  obtain Y hY from h3; conditional at hY
  define; fix X; assume hX
  have h4 := by apply h1 X hX Y hY.left
  apply h2 at h4; define at h4
  disj_syll h4 hY.right
  apply h4
  done

-- 7.
theorem Exercise_3_5_24a (U : Type) (A B C : Set U) :
    (A ∪ B) ∆ C ⊆ (A ∆ C) ∪ (B ∆ C) := by
  define; fix a; assume h1; define at h1; define
  by_cases on h1
  · define at h1
    have h2 := h1.left; define at h2
    by_cases on h2
    · apply Or.inl; define; apply Or.inl; define
      apply And.intro h2 h1.right
    · apply Or.inr; define; apply Or.inl; define
      apply And.intro h2 h1.right
  · define at h1
    have h2 := h1.right; define at h2; demorgan at h2
    apply Or.inl; define; apply Or.inr; define
    apply And.intro h1.left h2.left
  done

/- Section 3.6 -/
-- 1.
theorem Exercise_3_4_15 (U : Type) (B : Set U) (F : Set (Set U)) :
    ⋃₀ {X : Set U | ∃ (A : Set U), A ∈ F ∧ X = A \ B}
      ⊆ ⋃₀ (F \ 𝒫 B) := by
  define; fix a; assume h; define at h
  obtain X h1 from h; clear h
  have h2 := h1.left; define at h2; obtain A h3 from h2; clear h2
  have h2 := h1.right; clear h1
  define; exists A
  apply And.intro
  · define; apply And.intro h3.left
    define; quant_neg; exists a
    rewrite [h3.right] at h2; define at h2
    conditional; apply h2
  · rewrite [h3.right] at h2; define at h2
    apply h2.left
  done

-- 2.
theorem Exercise_3_5_9 (U : Type) (A B : Set U)
    (h1 : 𝒫 (A ∪ B) = 𝒫 A ∪ 𝒫 B) : A ⊆ B ∨ B ⊆ A := by
  --Hint:  Start like this:
  have h2 : A ∪ B ∈ 𝒫 (A ∪ B) := by
    define; fix a; assume h; apply h
    done
  rewrite [h1] at h2
  define at h2
  by_cases on h2
  · define at h2
    apply Or.inr; define; fix a; assume h
    apply h2; define; apply Or.inr h
  · define at h2
    apply Or.inl; define; fix a; assume h
    apply h2; define; apply Or.inl h
  done

-- 3.
theorem Exercise_3_6_6b (U : Type) :
    ∃! (A : Set U), ∀ (B : Set U), A ∪ B = A := by
  exists_unique
  · --existence
    exists {x: U|True}
    fix B
    apply Set.ext; fix x
    apply Iff.intro
    · assume h; define; trivial
    · assume h; define; apply Or.inl h
  · --uniqueness
    fix A1; fix A2
    assume h1; assume h2
    have h3 := by apply h1 A2
    have h4 := by apply h2 A1
    rewrite [← h3]
    nth_rewrite 2 [← h4]
    apply union_comm
  done

-- 4.
theorem Exercise_3_6_7b (U : Type) :
    ∃! (A : Set U), ∀ (B : Set U), A ∩ B = A := by
  exists_unique
  · -- existence
    exists ∅ ; fix B; apply Set.ext; fix x
    apply Iff.intro
    · assume h; define at h; apply h.left
    · assume h; define at h; by_contra h1; apply h
  · -- uniqueness
    -- lemma: intersection_comm
    have h: ∀ (A B: Set U), A ∩ B = B ∩ A := by
      fix A; fix B; apply Set.ext; fix x;
      apply Iff.intro
      · assume h; define; define at h; apply And.intro h.right h.left
      · assume h; define; define at h; apply And.intro h.right h.left
      done

    fix A1; fix A2; assume h1; assume h2
    have h3 := by apply h1 A2
    have h4 := by apply h2 A1
    rewrite [h] at h3
    rewrite [h3] at h4
    apply h4
  done

-- 5.
theorem Exercise_3_6_8a (U : Type) : ∀ (A : Set U),
    ∃! (B : Set U), ∀ (C : Set U), C \ A = C ∩ B := by
  fix A; exists_unique
  · --existence
    exists {x: U|x ∉ A}; fix C; apply Set.ext
    fix x; apply Iff.intro
    · assume h; define at h; define; apply And.intro h.left _
      define; apply h.right
    · assume h; define at h; define; apply And.intro h.left _
      have h1 := h.right; define at h1; apply h1
  · --uniqueness
    fix B1; fix B2; assume h1; assume h2
    have h3 := by apply h1 (B1 ∪ B2)
    have h4 := by apply h2 (B1 ∪ B2)
    have h: ∀ (A B: Set U), (A ∪ B) ∩ A = A := by
      fix C1; fix C2; apply Set.ext; fix x
      apply Iff.intro
      · assume h; define at h; apply h.right
      · assume h; define; apply And.intro _ h; define; apply Or.inl h
      done
    rewrite [h, union_comm] at h3
    rewrite [union_comm, h, h3] at h4
    apply h4
  done

-- 6.
theorem Exercise_3_6_10 (U : Type) (A : Set U)
    (h1 : ∀ (F : Set (Set U)), ⋃₀ F = A → A ∈ F) :
    ∃! (x : U), x ∈ A := by
  --Hint:  Start like this:
  set F0 : Set (Set U) := {X : Set U | X ⊆ A ∧ ∃! (x : U), x ∈ X}
  --Now F0 is in the tactic state, with the definition above
  have h2 : ⋃₀ F0 = A := by
    apply Set.ext; fix x; apply Iff.intro
    · assume h; define at h; obtain X h2 from h
      have h3 := h2.left; define at h3
      have h4 := h3.left; define at h4; apply h4; apply h2.right
    · assume h; define; exists {x}; apply And.intro
      · define; apply And.intro;
        · define; fix a; assume ha; define at ha; rewrite [ha]; apply h
        · exists_unique; exists x; fix y; fix z; assume hy; assume hz
          define at hy; define at hz; rewrite [hy, hz]; eq_refl
      · define; eq_refl
    done
  apply h1 at h2; define at h2
  apply h2.right
  done

/- Section 3.7 -/
-- 1.
theorem Exercise_3_3_18a (a b c : Int)
    (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ (b + c) := by
  define at h1; obtain k1 hk1 from h1
  define at h2; obtain k2 hk2 from h2
  define; exists (k1 + k2); rw [hk1, hk2]; ring
  done

-- 2.
theorem Exercise_3_4_6 (U : Type) (A B C : Set U) :
    A \ (B ∩ C) = (A \ B) ∪ (A \ C) := by
  apply Set.ext
  fix x : U
  show x ∈ A \ (B ∩ C) ↔ x ∈ A \ B ∪ A \ C from
    calc x ∈ A \ (B ∩ C)
      _ ↔ x ∈ A ∧ ¬(x ∈ B ∧ x ∈ C) := by rfl
      _ ↔ x ∈ A ∧ (x ∉ B ∨ x ∉ C) := by demorgan: (x ∉ B ∨ x ∉ C); rfl
      _ ↔ (x ∈ A ∧ x ∉ B) ∨ (x ∈ A ∧ x ∉ C) := by apply and_or_left
      _ ↔ x ∈ (A \ B) ∪ (A \ C) := by rfl
  done

-- 3.
theorem Exercise_3_4_10 (x y : Int)
    (h1 : odd x) (h2 : odd y) : even (x - y) := by
  define at h1; obtain k1 hk1 from h1
  define at h2; obtain k2 hk2 from h2
  define; exists (k1 - k2); rw [hk1, hk2]; ring
  done

-- 4.
theorem Exercise_3_4_27a :
    ∀ (n : Int), 15 ∣ n ↔ 3 ∣ n ∧ 5 ∣ n := by
    fix n; apply Iff.intro
    · assume h; define at h; obtain k hk from h
      apply And.intro
      · define; exists 5 * k; rw [hk]; ring
      · define; exists 3 * k; rw [hk]; ring
    · assume h; have h1 := h.left; have h2 := h.right
      define at h1; obtain k1 hk1 from h1
      define at h2; obtain k2 hk2 from h2
      define; exists (2*k2-k1); rewrite [hk2] at hk1
      rewrite [hk2]; ring
      have h3: k1 * 15 = 5 * (5 * k2) := by rw [hk1]; ring
      rw [h3]; ring

-- 5.
theorem Like_Exercise_3_7_5 (U : Type) (F : Set (Set U))
    (h1 : 𝒫 (⋃₀ F) ⊆ ⋃₀ {𝒫 A | A ∈ F}) :
    ∃ (A : Set U), A ∈ F ∧ ∀ (B : Set U), B ∈ F → B ⊆ A := by
  define at h1
  exists ⋃₀ F; apply And.intro
  · -- ⋃₀ F ∈ F
    have h: ⋃₀ F ∈ 𝒫 ⋃₀ F := by
      define; fix x; assume h; apply h
    have h2 := by apply h1 h
    clear h1; clear h
    define at h2; obtain X h3 from h2; clear h2
    have h5 := h3.left; have h4 := h3.right; clear h3
    define at h5; obtain Y h6 from h5; clear h5
    have h: ⋃₀ F = Y := by
      apply Set.ext; fix x
      apply Iff.intro
      · -- ->
        assume h1; rw [←h6.right] at h4; define at h4
        apply h4; apply h1
      · -- <-
        assume h1; define; exists Y; apply And.intro h6.left h1
      done
    rewrite [h]; apply h6.left
  · --
    fix B; assume h; define
    fix x; assume hx
    define; exists B
  done
