theory Refine_C_AC
imports
  "../lib/ComCorres"
  "../AutoCorres/Impl"
begin

lemma refines: "C_minimal \<sqsubseteq> AC_minimal"
proof -
  let ?m\<^sub>A = "minimalAC" and ?m\<^sub>C = "Call minimal_'proc"
    and ?\<Gamma> = "minimal_global_addresses.\<Gamma>" and ?P = "(\<lambda>s. True)"
    and ?st = "minimal.lift_global_heap \<circ> globals"
    and ?rx = "sint \<circ> ret__int_'"
  have "Run AC_minimal = lift_nd ?m\<^sub>A" unfolding AC_minimal_def by simp
  moreover have "Run C_minimal = lift_com ?m\<^sub>C ?\<Gamma>" unfolding C_minimal_def by simp
  moreover have "\<forall>s s\<^sub>C. s\<^sub>C \<in> Init C_minimal s \<longrightarrow>
       ?P s\<^sub>C \<and> \<not> snd (minimal.minimal' (?st s\<^sub>C)) \<and> ?st s\<^sub>C \<in> Init AC_minimal s"
    unfolding C_minimal_def AC_minimal_def minimal.minimal'_def
    by (simp add: snd_return)
  moreover have "ac_corres ?st ?\<Gamma> ?rx ?P ?m\<^sub>A ?m\<^sub>C" using minimal.minimal'_ac_corres .
  moreover have "\<forall>s\<^sub>C'. Fin AC_minimal (?st s\<^sub>C') = Fin C_minimal s\<^sub>C'"
    unfolding AC_minimal_def C_minimal_def by simp
  ultimately show ?thesis by (metis corres_refines snd_liftE)
qed

end