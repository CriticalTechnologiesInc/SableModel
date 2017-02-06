theory TPM_Relation
imports
  "../Abstract/TPM"
  "../AutoCorres/Impl"
begin

definition
  PCRINDEX_rel :: "TPM.PCRINDEX \<Rightarrow> 32 word \<Rightarrow> bool"
where
  "PCRINDEX_rel i i' \<equiv>
    case i of
      PCR0 \<Rightarrow> i' = 0
    | PCR1 \<Rightarrow> i' = 1
    | PCR2 \<Rightarrow> i' = 2
    | PCR3 \<Rightarrow> i' = 3
    | PCR4 \<Rightarrow> i' = 4
    | PCR5 \<Rightarrow> i' = 5
    | PCR6 \<Rightarrow> i' = 6
    | PCR7 \<Rightarrow> i' = 7
    | PCR8 \<Rightarrow> i' = 8
    | PCR9 \<Rightarrow> i' = 9
    | PCR10 \<Rightarrow> i' = 10
    | PCR11 \<Rightarrow> i' = 11
    | PCR12 \<Rightarrow> i' = 12
    | PCR13 \<Rightarrow> i' = 13
    | PCR14 \<Rightarrow> i' = 14
    | PCR15 \<Rightarrow> i' = 15
    | PCR16 \<Rightarrow> i' = 16
    | PCR17 \<Rightarrow> i' = 17
    | PCR18 \<Rightarrow> i' = 18
    | PCR19 \<Rightarrow> i' = 19
    | PCR20 \<Rightarrow> i' = 20
    | PCR21 \<Rightarrow> i' = 21
    | PCR22 \<Rightarrow> i' = 22
    | PCR23 \<Rightarrow> i' = 23"

value "PCRINDEX_rel PCR7 7" (* True *)
value "PCRINDEX_rel PCR7 8" (* False *)
value "PCRINDEX_rel PCR7 90" (* False *)

definition "TPM_BASE \<equiv> 0 :: 32 word"
definition "TPM_SUCCESS \<equiv> TPM_BASE"

definition
  ERROR_rel :: "TPM.ERROR \<Rightarrow> 32 word \<Rightarrow> bool"
where
  "ERROR_rel e e' \<equiv> if e' = TPM_BASE then False else
    case e of
      AUTHFAIL \<Rightarrow> e' = TPM_BASE + 1
    | OTHER_ERROR \<Rightarrow> e' > TPM_BASE + 1 \<and> e' \<le> TPM_BASE + 99"

value "ERROR_rel AUTHFAIL 1" (* True *)
value "ERROR_rel OTHER_ERROR 1" (* False *)

definition
  RESULT_rel :: "(TPM.ERROR + unit) \<Rightarrow> 32 word \<Rightarrow> bool"
where
  "RESULT_rel r r' \<equiv>
    case r of
      Inl error \<Rightarrow> ERROR_rel error r'
    | Inr _ \<Rightarrow> r' = TPM_SUCCESS"

value "RESULT_rel (Inr ()) 0" (* True *)
value "RESULT_rel (Inr ()) 1" (* False *)
value "RESULT_rel (Inl AUTHFAIL) 1" (* True *)

definition
  DIGEST_rel :: "TPM.DIGEST \<Rightarrow> tdTPM_DIGEST_C \<Rightarrow> bool"
where
  "DIGEST_rel d d' \<equiv> True"

end