import HTPILib.HTPIDefs
namespace HTPI

theorem Example_3_2_4
    (P Q R : Prop) (h : P → (Q → R)) : ¬R → (P → ¬Q) := by
  assume h2 : ¬R
  assume h3 : P
  have h4 : Q → R := h h3
  contrapos at h4            --Now h4 : ¬R → ¬Q
  show ¬Q from h4 h2
  done

theorem very_easy
    (P Q : Prop) (h1 : P → Q) (h2 : P) : Q := h1 h2

theorem two_imp (P Q R : Prop)
    (h1 : P → Q) (h2 : Q → ¬R) : R → ¬P := by
  contrapos
  assume h3 : P
  have h4 : Q := h1 h3
  show ¬R from h2 h4
  done

theorem easy (P Q R : Prop) (h1 : P → Q)
    (h2 : Q → R) (h3 : P) : R := h2 (h1 h3)
