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

end