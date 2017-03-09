theory RRelation
imports
  TPM_Relation
begin

type_synonym 'a value_rel = "'a \<Rightarrow> heap_data \<times> lifted_globals \<Rightarrow> bool"

definition
  RESULT_rel :: "ERROR + unit \<Rightarrow> tdRESULT_C \<Rightarrow> bool"
where
  "RESULT_rel r r' \<equiv>
    case r of
      Inl error \<Rightarrow> ERROR_rel error (tdEXCEPTION_C.error_C (tdRESULT_C.exception_C r'))
    | Inr value \<Rightarrow> tdEXCEPTION_C.error_C (tdRESULT_C.exception_C r') = NONE"

definition
  R_AUTHDATA_rel :: "ERROR + TPM.AUTHDATA \<Rightarrow> TPM_AUTHDATA_exception_C \<Rightarrow> bool"
where
  "R_AUTHDATA_rel a a' \<equiv>
    case a of
      Inl error \<Rightarrow> ERROR_rel error (tdEXCEPTION_C.error_C (TPM_AUTHDATA_exception_C.exception_C a'))
    | Inr value \<Rightarrow> tdEXCEPTION_C.error_C (TPM_AUTHDATA_exception_C.exception_C a') = NONE
        \<and> AUTHDATA_rel value (TPM_AUTHDATA_exception_C.value_C a')"

definition
  R_NONCE_rel :: "ERROR + TPM.NONCE \<Rightarrow> TPM_NONCE_exception_C \<Rightarrow> bool"
where
  "R_NONCE_rel a a' \<equiv>
    case a of
      Inl error \<Rightarrow> ERROR_rel error (tdEXCEPTION_C.error_C (TPM_NONCE_exception_C.exception_C a'))
    | Inr value \<Rightarrow> tdEXCEPTION_C.error_C (TPM_NONCE_exception_C.exception_C a') = NONE
        \<and> NONCE_rel value (TPM_NONCE_exception_C.value_C a')"

definition
  R_PCRVALUE_rel :: "(ERROR + TPM.DIGEST) \<Rightarrow> TPM_PCRVALUE_exception_C \<Rightarrow> bool"
where
  "R_PCRVALUE_rel a a' \<equiv>
    case a of
      Inl error \<Rightarrow> ERROR_rel error (tdEXCEPTION_C.error_C (TPM_PCRVALUE_exception_C.exception_C a'))
    | Inr value \<Rightarrow> tdEXCEPTION_C.error_C (TPM_PCRVALUE_exception_C.exception_C a') = NONE
        \<and> DIGEST_rel value (TPM_PCRVALUE_exception_C.value_C a')"

definition
  HEAP_DATA_rel :: "('a :: Hashable) value_rel \<Rightarrow> 'a \<Rightarrow> tdHEAP_DATA_C \<times> lifted_globals \<Rightarrow> bool"
where
  "HEAP_DATA_rel vrel v v' \<equiv> vrel v ((tdHEAP_DATA_C.data_C (fst v'),
        tdHEAP_DATA_C.dataSize_C (fst v')), snd v')"

definition
  R_HEAP_DATA_rel :: "('a :: Hashable) value_rel
                      \<Rightarrow> (ERROR + 'a) \<Rightarrow> HEAP_DATA_exception_C \<times> lifted_globals \<Rightarrow> bool"
where
  "R_HEAP_DATA_rel vrel v v' \<equiv>
    case v of
      Inl error \<Rightarrow> ERROR_rel error (tdEXCEPTION_C.error_C (HEAP_DATA_exception_C.exception_C (fst v')))
    | Inr value \<Rightarrow> tdEXCEPTION_C.error_C (HEAP_DATA_exception_C.exception_C (fst v')) = NONE
        \<and> HEAP_DATA_rel vrel value (HEAP_DATA_exception_C.value_C (fst v'), snd v')"

definition
  R_STORED_DATA_rel :: "('a :: Hashable) value_rel \<Rightarrow> (ERROR + 'a TPM.STORED_DATA)
                        \<Rightarrow> TPM_STORED_DATA12_exception_C \<times> lifted_globals \<Rightarrow> bool"
where
  "R_STORED_DATA_rel vrel d d' \<equiv>
    case d of
      Inl error \<Rightarrow> ERROR_rel error (tdEXCEPTION_C.error_C (TPM_STORED_DATA12_exception_C.exception_C (fst d')))
    | Inr value \<Rightarrow> tdEXCEPTION_C.error_C (TPM_STORED_DATA12_exception_C.exception_C (fst d')) = NONE
        \<and> STORED_DATA_rel vrel value ((TPM_STORED_DATA12_exception_C.value_C (fst d')), snd d')"

definition (in sable_isa)
  E_STORED_DATA_rel :: "('a :: Hashable) value_rel \<Rightarrow>
                        'a TPM.STORED_DATA \<Rightarrow> heap_data \<times> lifted_globals \<Rightarrow> bool"
where
  "E_STORED_DATA_rel vrel d d' \<equiv> case d' of ((v', size'), s') \<Rightarrow>
    \<forall>p \<in> fst (unpack_TPM_STORED_DATA12' v' size' s'). STORED_DATA_rel vrel d p"

(* FIXME *)
definition
  string_rel :: "string \<Rightarrow> heap_data \<times> lifted_globals \<Rightarrow> bool"
where
  "string_rel s s' \<equiv> True"

end