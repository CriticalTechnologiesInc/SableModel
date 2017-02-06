theory Refines
imports
  Refine_A_ACL
  Refine_AC_A
  Refine_C_AC
begin

theorem refines: "C_minimal \<sqsubseteq> ACL_minimal"
using Refine_C_AC.refines Refine_AC_A.refines Refine_A_ACL.refines
by (meson refinement_trans)

end