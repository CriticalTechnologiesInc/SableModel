theory TPM
imports
  "../lib/NondetExtensions"
begin

datatype 'a Enc = encrypt 'a

(* External Structures, from TPM Main Part 2 *)

datatype PCRINDEX = PCR0 | PCR1 | PCR2 | PCR3 | PCR4 | PCR5 | PCR6 | PCR7 | PCR8 | PCR9 | PCR10
| PCR11 | PCR12 | PCR13 | PCR14 | PCR15 | PCR16 | PCR17 | PCR18 | PCR19 | PCR20 | PCR21 | PCR22
| PCR23
type_synonym PCR_SELECTION = "PCRINDEX set"

datatype LOCALITY = LOC_ZERO | LOC_ONE | LOC_TWO | LOC_THREE | LOC_FOUR
type_synonym LOCALITY_SELECTION = "LOCALITY set"

type_synonym NV_INDEX = nat

datatype ERROR = AUTHFAIL | OTHER_ERROR

type_synonym RESULT = "ERROR + unit"
type_synonym AUTHHANDLE = nat

datatype NONCE = nonce nat

(* FIXME: fill this in? *)
typedecl ENTITY_TYPE

(* FIXME: fill this in? *)
datatype PAYLOAD_TYPE = PT_SEAL

(* helper type *)
datatype dig =
  PCRINDEX_dig PCRINDEX
| PCR_SELECTION_dig PCR_SELECTION
| NV_INDEX_dig NV_INDEX
| RESULT_dig RESULT
| AUTHHANDLE_dig AUTHHANDLE
| AUTHDATA_dig AUTHDATA
| NONCE_dig NONCE
| ENTITY_TYPE_dig ENTITY_TYPE
| PAYLOAD_TYPE_dig PAYLOAD_TYPE
| LOCALITY_SELECTION_dig LOCALITY_SELECTION
| char_dig char
| nat_dig nat
| bool_dig bool
| DIGEST_dig "dig list"
| Enc_dig (* hash of encrypted data *)
and AUTHDATA = auth nat | hmac AUTHDATA "dig list"

type_synonym DIGEST = "dig list"

(* Hashable instances for atomic types *)

class Hashable =
  fixes hash :: "'a \<Rightarrow> DIGEST"
  assumes injective: "hash x = hash y \<Longrightarrow> x = y"

instantiation unit :: Hashable
begin
definition "hash_unit \<equiv> \<lambda>_ :: unit. Nil :: DIGEST"
instance proof
  fix x y :: unit
  assume "hash x = hash y"
  thus "x = y" by auto
qed
end

instantiation char :: Hashable
begin
definition "hash_char c \<equiv> [char_dig c]"
instance proof
  fix x y :: char
  assume "hash x = hash y"
  thus "x = y" unfolding hash_char_def by simp
qed
end

instantiation list :: (Hashable) Hashable
begin
definition "hash_list = map (DIGEST_dig \<circ> hash)"
instance proof
  fix xs ys :: "'a list"
  assume "hash xs = hash ys"
  thus "xs = ys" unfolding hash_list_def
  proof (induction ys arbitrary: xs)
    case Nil thus "xs = []" by simp
  next
    fix y :: 'a and xs'' ys' :: "'a list"
    assume IH: "\<And>xs. map (DIGEST_dig \<circ> hash) xs = map (DIGEST_dig \<circ> hash) ys' \<Longrightarrow> xs = ys'"
       and xs'': "map (DIGEST_dig \<circ> hash) xs'' = map (DIGEST_dig \<circ> hash) (y # ys')"
    { assume "xs'' = Nil"
      with xs'' have False by auto
      hence "xs'' = y # ys'" .. }
    moreover
    { fix x xs'
      assume a: "xs'' = x # xs'"
      with xs'' have "map (DIGEST_dig \<circ> hash) xs' = map (DIGEST_dig \<circ> hash) ys'" by simp
      hence "xs' = ys'" using IH by auto
      hence "x # xs' = y # ys'" using xs'' a and injective by auto
      with a have "xs'' = y # ys'" by simp }
    ultimately show "xs'' = y # ys'" using xs'' by auto
  qed
qed
end

instantiation Enc :: (Hashable) Hashable
begin
definition "hash_Enc e \<equiv> case e of encrypt d \<Rightarrow> [Enc_dig, DIGEST_dig (hash d)]"
instance proof
  fix x y :: "('a :: Hashable) Enc"
  assume "hash x = hash y"
  thus "x = y" unfolding hash_Enc_def
    apply (case_tac x)
    apply (case_tac y)
    apply (simp add: injective)
    done
qed
end

(* derived TPM types *)

record PCR_INFO_LONG =
  localityAtCreation :: LOCALITY_SELECTION
  localityAtRelease :: LOCALITY_SELECTION
  creationPCRSelection :: PCR_SELECTION
  releasePCRSelection :: PCR_SELECTION
  digestAtCreation :: DIGEST
  digestAtRelease :: DIGEST

instantiation PCR_INFO_LONG_ext :: (Hashable) Hashable
begin

definition "hash_PCR_INFO_LONG_ext i \<equiv>
  [LOCALITY_SELECTION_dig (localityAtCreation i),
   LOCALITY_SELECTION_dig (localityAtRelease i),
   PCR_SELECTION_dig (creationPCRSelection i),
   PCR_SELECTION_dig (releasePCRSelection i),
   DIGEST_dig (digestAtCreation i),
   DIGEST_dig (digestAtRelease i),
   DIGEST_dig (hash (more i))]"

instance proof
  fix x y :: "('a :: Hashable) PCR_INFO_LONG_scheme"
  assume "hash x = hash y"
  thus "x = y" unfolding hash_PCR_INFO_LONG_ext_def by (simp add: injective)
qed

end

record ('a :: Hashable) SEALED_DATA =
  payload :: PAYLOAD_TYPE
  authData :: AUTHDATA
  tpmProof :: AUTHDATA
  storedDigest :: DIGEST
  data :: 'a

instantiation SEALED_DATA_ext :: (Hashable, Hashable) Hashable
begin

definition "hash_SEALED_DATA_ext d \<equiv>
  [PAYLOAD_TYPE_dig (payload d),
   AUTHDATA_dig (authData d),
   AUTHDATA_dig (tpmProof d),
   DIGEST_dig (storedDigest d),
   DIGEST_dig (hash (data d)),
   DIGEST_dig (hash (more d))]"

instance proof
  fix x y :: "('a :: Hashable, 'z :: Hashable) SEALED_DATA_scheme"
  assume "hash x = hash y"
  thus "x = y" unfolding hash_SEALED_DATA_ext_def by (simp add: injective)
qed

end

record ('a :: Hashable) STORED_DATA =
  et :: ENTITY_TYPE
  pcrInfo :: PCR_INFO_LONG
  encData :: "('a SEALED_DATA) Enc"

instantiation STORED_DATA_ext :: (Hashable, Hashable) Hashable
begin

definition "hash_STORED_DATA_ext d \<equiv>
  [ENTITY_TYPE_dig (et d),
   DIGEST_dig (hash (pcrInfo d)),
   DIGEST_dig (hash (encData d)),
   DIGEST_dig (hash (more d))]"

instance proof
  fix x y :: "('a :: Hashable, 'z :: Hashable) STORED_DATA_scheme"
  assume "hash x = hash y"
  thus "x = y" unfolding hash_STORED_DATA_ext_def by (simp add: injective)
qed

end

(* auxiliary TPM Structures *)

record Auth_in =
  authHandle :: AUTHHANDLE
  nonceOdd :: NONCE
  continueAuthSession :: bool
  auth :: AUTHDATA

record Auth_out =
  nonceEven :: NONCE
  continueAuthSession :: bool
  auth :: AUTHDATA

(* TPM State representation *)

(*record Session =
  nonceEven :: NONCE
  nonceOdd :: "NONCE option"

type_synonym Session_map = "AUTHHANDLE \<Rightarrow> Session option"

definition
  Session_empty :: Session_map
where
  "Session_empty \<equiv> \<lambda>_. None"

definition
  update_Session :: "Session_map \<Rightarrow> AUTHHANDLE \<Rightarrow> Session \<Rightarrow> Session_map"
where
  "update_Session m h s \<equiv> \<lambda>h'. if h' = h then Some s else m h'"

record tpm_state =
  sessions :: Session_map*)

type_synonym tpm_state = unit
type_synonym 'a tpm_monad = "(tpm_state, 'a) nondet_monad"

(* TPM Commands, from TPM Main Part 3 *)

record PCRRead_in =
  pcrIndex :: PCRINDEX

record PCRRead_out =
  returnCode :: RESULT
  outDigest :: DIGEST

definition
  PCRRead :: "PCRRead_in \<Rightarrow> PCRRead_out tpm_monad"
where
  "PCRRead com \<equiv> select (UNIV :: PCRRead_out set)"

record OIAP_out =
  returnCode :: RESULT
  authHandle :: AUTHHANDLE
  nonceEven :: NONCE

definition
  OIAP :: "OIAP_out tpm_monad"
where
  "OIAP \<equiv> unknown"

record NV_ReadValue_in =
  nvIndex :: NV_INDEX
  offset :: nat
  ownerAuth :: "Auth_in option"

record 'a NV_ReadValue_out =
  returnCode :: RESULT
  data :: 'a
  ownerAuth :: Auth_out

definition
  NV_ReadValue :: "NV_ReadValue_in \<Rightarrow> ('a NV_ReadValue_out) tpm_monad"
where
  "NV_ReadValue com \<equiv> unknown"

end