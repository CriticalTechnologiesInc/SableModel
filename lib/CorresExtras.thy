theory CorresExtras
imports
  Corres_UL
begin

lemma corres_noop_r[intro]:
  assumes "\<And>s'. P' s' \<Longrightarrow>
    \<lbrace>\<lambda>s. (s, s') \<in> sr \<and> P s\<rbrace> f \<exists>\<lbrace>\<lambda>rv s. (s, s') \<in> sr \<and> r rv (rv', s')\<rbrace>"
  shows "corres_underlying sr nf nf' r P P' f (return rv')"
unfolding corres_underlying_def return_def using assms
by (auto simp add: exs_valid_def)

(*lemma corres_valid[intro]:
  fixes s\<^sub>A
  assumes corres: "corres_underlying sr nf nf' rr P P' m m'"
      and valid: "\<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>"
      and rel: "\<forall>s\<^sub>C r r'. (s\<^sub>A, s') \<in> sr \<forall>r r'. rr r (r', s') \<and> Q r s \<longrightarrow> Q' r' s'"
  shows "\<lbrace>P'\<rbrace> m' \<lbrace>Q'\<rbrace>"
unfolding valid_def
proof clarify
  fix s\<^sub>C s\<^sub>C' r'
  assume "P' s\<^sub>C" and "(r', s\<^sub>C') \<in> fst (m' s\<^sub>C)"
  { assume "\<exists>s\<^sub>A. (s\<^sub>A, s\<^sub>C) \<in> sr"
    then obtain s\<^sub>A where "(s\<^sub>A, s\<^sub>C) \<in> sr" by auto
    from corres
  show "Q' r' s\<^sub>C'"*)

end