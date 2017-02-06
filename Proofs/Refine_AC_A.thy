theory Refine_AC_A
imports
  "../AutoCorres/Impl"
  "../Abstract/Abstract"
  "../lib/NondetCorres"
begin

definition "R \<equiv> UNIV :: (astate \<times> lifted_globals) set"
definition "I\<^sub>C \<equiv> UNIV :: lifted_globals set"
definition "I\<^sub>A \<equiv> UNIV :: astate set"

(*lemma corres: "corres_underlying R False True \<top>\<top>
  (\<lambda>s\<^sub>A. s\<^sub>A \<in> I\<^sub>A) (\<lambda>s\<^sub>C. s\<^sub>C \<in> I\<^sub>C) minimalA minimalAC"
unfolding minimalA_def minimal.minimal'_def
apply (rule Corres_UL.corres_noop)
apply wp
apply (auto simp: no_fail_def R_def return_def)
done

lemma refines: "AC_minimal \<sqsubseteq> A_minimal"
proof (rule sim_imp_refines)
  have "A_minimal \<Turnstile> I\<^sub>A" unfolding I\<^sub>A_def by auto
  moreover have "AC_minimal \<Turnstile> I\<^sub>C" unfolding I\<^sub>C_def by auto
  moreover have "LI A_minimal AC_minimal R (I\<^sub>A \<times> I\<^sub>C)"
  proof -
    have "Run A_minimal = lift_nd minimalA" unfolding A_minimal_def by simp
    moreover have "Run AC_minimal = lift_nd minimalAC" unfolding AC_minimal_def by simp
    moreover have "\<forall>s. Init AC_minimal s \<subseteq> (R \<inter> I\<^sub>A \<times> I\<^sub>C) `` Init A_minimal s"
      unfolding AC_minimal_def A_minimal_def R_def I\<^sub>A_def I\<^sub>C_def by auto
    moreover have "corres_underlying R False True \<top>\<top>
      (\<lambda>s\<^sub>A. s\<^sub>A \<in> I\<^sub>A) (\<lambda>s\<^sub>C. s\<^sub>C \<in> I\<^sub>C) minimalA minimalAC" using corres .
    moreover have "\<forall>s s'. (s, s') \<in> R \<inter> I\<^sub>A \<times> I\<^sub>C \<longrightarrow> Fin AC_minimal s' = Fin A_minimal s"
      unfolding AC_minimal_def A_minimal_def R_def I\<^sub>A_def I\<^sub>C_def by auto
    ultimately show ?thesis using corres_LI by blast
  qed
  ultimately show "AC_minimal \<sqsubseteq>\<^sub>F A_minimal"
    using LI_fw_sim and L_invariantI by blas
qed*)

end