theory WP_Extras
imports
  "nicta_lib/Monad_WP/wp/WPEx"
begin

lemma exs_valid_modify[wp]: "\<lbrace>\<lambda>s. Q () (f s)\<rbrace> modify f \<exists>\<lbrace>Q\<rbrace>"
  unfolding modify_def
  apply (rule exs_valid_bind [where B = "\<lambda>s _. Q () (f s)"])
  apply (auto simp add: exs_valid_def get_def put_def)
done

end