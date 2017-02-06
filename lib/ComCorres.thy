chapter {* Define correspondence between a non-deterministic monad with failure,
  and a C-SIMP computation *}

theory ComCorres
imports
  CorresExtras
  NondetExtensions
  ComExtensions
begin

lemma corres_refines[dest]:
  fixes C A st rx P m\<^sub>A m\<^sub>C \<Gamma>
  assumes ndA: "Run A = lift_nd m\<^sub>A"
      and comC: "Run C = lift_com m\<^sub>C \<Gamma>"
      and init: "\<forall>s s\<^sub>C. s\<^sub>C \<in> Init C s \<longrightarrow> P s\<^sub>C \<and> \<not> snd (m\<^sub>A (st s\<^sub>C)) \<and> st s\<^sub>C \<in> Init A s"
      and corres: "ac_corres st \<Gamma> rx P m\<^sub>A m\<^sub>C"
      and fin: "\<forall>s\<^sub>C'. Fin A (st s\<^sub>C') = Fin C s\<^sub>C'"
  shows "C \<sqsubseteq> A"
unfolding refines_def
proof clarify
  fix s s'
  assume "s' \<in> execution C s"
  hence "s' \<in> Fin C ` Run C `` Init C s" unfolding execution_def .
  hence "\<exists>s\<^sub>C s\<^sub>C'. s\<^sub>C \<in> Init C s \<and> (s\<^sub>C, s\<^sub>C') \<in> Run C \<and> (s' = Fin C s\<^sub>C')" by auto
  then obtain s\<^sub>C and s\<^sub>C' where i: "s\<^sub>C \<in> Init C s" and r: "(s\<^sub>C, s\<^sub>C') \<in> Run C"
    and f: "s' = Fin C s\<^sub>C'" by auto
  let ?s\<^sub>A = "st s\<^sub>C" and ?s\<^sub>A' = "st s\<^sub>C'" and ?r\<^sub>A' = "rx s\<^sub>C'"
  from i and init have "P s\<^sub>C" and "\<not> snd (m\<^sub>A ?s\<^sub>A)" and "?s\<^sub>A \<in> Init A s" by auto
  with corres have corr: "\<forall>t. \<Gamma> \<turnstile> \<langle>m\<^sub>C, Normal s\<^sub>C\<rangle> \<Rightarrow> t \<longrightarrow>
           (\<exists>s\<^sub>C'. t = Normal s\<^sub>C' \<and> (Inr (rx s\<^sub>C'), st s\<^sub>C') \<in> fst (m\<^sub>A ?s\<^sub>A))" and
           "\<Gamma> \<turnstile> m\<^sub>C \<down> Normal s\<^sub>C" unfolding ac_corres_def by auto
  from r and comC have "\<Gamma>\<turnstile> \<langle>m\<^sub>C, Normal s\<^sub>C\<rangle> \<Rightarrow> Normal s\<^sub>C'" unfolding lift_com_def by simp
  with corr have "(Inr ?r\<^sub>A', ?s\<^sub>A') \<in> fst (m\<^sub>A ?s\<^sub>A)" by auto
  hence "(?s\<^sub>A, ?s\<^sub>A') \<in> Run A" using ndA unfolding lift_nd_def by auto
  moreover from i and init have "?s\<^sub>A \<in> Init A s" by auto
  moreover from fin have "Fin A ?s\<^sub>A' = Fin C s\<^sub>C'" ..
  ultimately show "s' \<in> execution A s" using f unfolding execution_def
    by (metis ImageI imageI)
qed

end