chapter {* Define correspondence between two non-deterministic monads with failure *}

theory NondetCorres
imports
  CorresExtras
  NondetExtensions
begin

lemma corres_LI[dest]:
  fixes C A R I\<^sub>A I\<^sub>C nf\<^sub>C m\<^sub>A m\<^sub>C
  assumes ndA: "Run A = lift_nd m\<^sub>A"
      and ndC: "Run C = lift_nd m\<^sub>C"
      and init: "\<forall>s. Init C s \<subseteq> (R \<inter> I\<^sub>A \<times> I\<^sub>C) `` Init A s"
      and corres: "corres_underlying R False nf\<^sub>C \<top>\<top>
                  (\<lambda>s\<^sub>A. s\<^sub>A \<in> I\<^sub>A) (\<lambda>s\<^sub>C. s\<^sub>C \<in> I\<^sub>C) m\<^sub>A m\<^sub>C"
      and fin:  "\<forall>s s'. (s, s') \<in> R \<inter> I\<^sub>A \<times> I\<^sub>C \<longrightarrow> Fin C s' = Fin A s"
  shows "LI A C R (I\<^sub>A \<times> I\<^sub>C)"
proof -
  have "\<forall>s. Init C s \<subseteq> R `` Init A s" using init by auto
  moreover have "R \<inter> I\<^sub>A \<times> I\<^sub>C ;;; Run C \<subseteq> Run A ;;; R" unfolding rel_semi_def
  proof safe
    fix s\<^sub>A s\<^sub>C s\<^sub>C'
    assume "s\<^sub>A \<in> I\<^sub>A" and "s\<^sub>C \<in> I\<^sub>C" and "(s\<^sub>A, s\<^sub>C) \<in> R" and "(s\<^sub>C, s\<^sub>C') \<in> Run C"
    hence "\<forall>(r', s\<^sub>C') \<in> fst (m\<^sub>C s\<^sub>C). \<exists>(r, s\<^sub>A') \<in> fst (m\<^sub>A s\<^sub>A). (s\<^sub>A', s\<^sub>C') \<in> R"
      and "nf\<^sub>C \<longrightarrow> \<not> snd (m\<^sub>C s\<^sub>C)" using corres unfolding corres_underlying_def by auto
    moreover from ndC and `(s\<^sub>C, s\<^sub>C') \<in> Run C` have "\<exists>r. (r, s\<^sub>C') \<in> fst (m\<^sub>C s\<^sub>C)"
      unfolding lift_nd_def mresults_def by auto
    ultimately have "\<exists>(r, s\<^sub>A') \<in> fst (m\<^sub>A s\<^sub>A). (s\<^sub>A', s\<^sub>C') \<in> R" by auto
    then obtain r and s\<^sub>A' where "(r, s\<^sub>A') \<in> fst (m\<^sub>A s\<^sub>A)" and "(s\<^sub>A', s\<^sub>C') \<in> R" by auto
    with ndA have "(s\<^sub>A, s\<^sub>A') \<in> Run A" unfolding lift_nd_def mresults_def by auto
    with `(s\<^sub>A', s\<^sub>C') \<in> R` show "(s\<^sub>A, s\<^sub>C') \<in> Run A O R" by auto
  qed
  moreover have "\<forall>s s'. (s, s') \<in> R \<inter> I\<^sub>A \<times> I\<^sub>C \<longrightarrow> Fin C s' = Fin A s" using fin by auto
  ultimately show ?thesis unfolding LI_def by simp
qed

end