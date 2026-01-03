import HTPILib.HTPIDefs
namespace HTPI

theorem extremely_easy (P : Prop) (h : P) : P := h

theorem very_easy
    (P Q : Prop) (h1 : P → Q) (h2 : P) : Q := h1 h2

theorem easy (P Q R : Prop) (h1 : P → Q)
    (h2 : Q → R) (h3 : P) : R := h2 (h1 h3)

theorem two_imp (P Q R : Prop)
    (h1 : P → Q) (h2 : Q → ¬R) : R → ¬P := by
    contrapos
    assume h3: P
    have h4: Q := h1 h3
    show ¬ R from h2 h4
    done

theorem Example_3_2_5_simple_general
    (U : Type) (B C : Set U) (a : U)
    (h1 : a ∈ B) (h2 : a ∉ B \ C) : a ∈ C := by
    define at h2
    demorgan at h2
    conditional at h2
    apply h2 h1
    done
