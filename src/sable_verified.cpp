# 1 "/Users/scottconstable/Documents/SU_Graduate/SABLE/sable/src/sable_verified.c"
# 1 "<built-in>" 1
# 1 "<built-in>" 3
# 330 "<built-in>" 3
# 1 "<command line>" 1
# 1 "<built-in>" 2
# 1 "/Users/scottconstable/Documents/SU_Graduate/SABLE/sable/src/sable_verified.c" 2
# 1 "/Users/scottconstable/Documents/SU_Graduate/SABLE/sable/build/include/sable_verified.h" 1

void reboot(void)__attribute__((noreturn));
typedef unsigned long UINT32;
UINT32 memcmp(const void *buf1,const void *buf2,UINT32 size);
void trusted_boot(void);
typedef struct TPM_Unseal_ret TPM_Unseal_ret;
typedef UINT32 TPM_RESULT;
typedef unsigned char BYTE;
struct TPM_Unseal_ret {
  TPM_RESULT returnCode;
  UINT32 dataSize;
  BYTE *data;
};
typedef struct tdTPM_STORED_DATA12 tdTPM_STORED_DATA12;
typedef unsigned short UINT16;
typedef UINT16 TPM_STRUCTURE_TAG;
typedef UINT16 TPM_ENTITY_TYPE;






struct tdTPM_STORED_DATA12 {
  TPM_STRUCTURE_TAG tag;
  TPM_ENTITY_TYPE et;
  UINT32 sealInfoSize;

  BYTE *sealInfo;
  UINT32 encDataSize;

  BYTE *encData;
};
typedef struct tdTPM_STORED_DATA12 TPM_STORED_DATA12;
typedef UINT32 TPM_KEY_HANDLE;
typedef struct tdTPM_AUTHDATA tdTPM_AUTHDATA;

struct tdTPM_AUTHDATA {
  BYTE authdata[0x14];
};
typedef struct tdTPM_AUTHDATA TPM_AUTHDATA;
typedef struct tdTPM_SESSION tdTPM_SESSION;
typedef UINT32 TPM_AUTHHANDLE;
typedef struct tdTPM_NONCE tdTPM_NONCE;

struct tdTPM_NONCE {
  BYTE nonce[0x14];
};
typedef struct tdTPM_NONCE TPM_NONCE;
typedef BYTE TPM_BOOL;
typedef struct tdTPM_OSAP_EXTENSION tdTPM_OSAP_EXTENSION;
struct tdTPM_OSAP_EXTENSION {
  TPM_NONCE nonceEvenOSAP;
  TPM_NONCE nonceOddOSAP;
};
typedef struct tdTPM_OSAP_EXTENSION TPM_OSAP_EXTENSION;
struct tdTPM_SESSION {
  TPM_AUTHHANDLE authHandle;
  TPM_NONCE nonceEven;
  TPM_NONCE nonceOdd;
  TPM_BOOL continueAuthSession;
  TPM_OSAP_EXTENSION *osap;
};
typedef struct tdTPM_SESSION TPM_SESSION;
struct TPM_Unseal_ret TPM_Unseal(TPM_STORED_DATA12 inData_in,TPM_KEY_HANDLE parentHandle_in,TPM_AUTHDATA parentAuth,TPM_SESSION **parentSession,TPM_AUTHDATA dataAuth,TPM_SESSION **dataSession);
const char *unseal_passphrase(TPM_AUTHDATA srk_auth,TPM_AUTHDATA pp_auth,TPM_STORED_DATA12 sealed_pp);
TPM_STORED_DATA12 unpack_TPM_STORED_DATA12(const BYTE *data,UINT32 dataSize);

typedef struct TPM_NV_ReadValue_ret TPM_NV_ReadValue_ret;
struct TPM_NV_ReadValue_ret {
  TPM_RESULT returnCode;
  UINT32 dataSize;
  BYTE *data;
};
typedef UINT32 TPM_NV_INDEX;





struct TPM_AUTHDATA_option { TPM_AUTHDATA value; char hasValue; };






struct TPM_NV_ReadValue_ret TPM_NV_ReadValue(TPM_NV_INDEX nvIndex_in,UINT32 offset_in,UINT32 dataSize_in,struct TPM_AUTHDATA_option ownerAuth_in,TPM_SESSION **session);
TPM_STORED_DATA12 read_passphrase(void);


typedef char bool;
int get_string(char *str,unsigned int strSize,bool show);

void out_string(const char *value);






void configure(void);
TPM_RESULT TPM_NV_WriteValueAuth(const BYTE *data_in,UINT32 dataSize_in,TPM_NV_INDEX nvIndex_in,UINT32 offset_in,TPM_AUTHDATA nv_auth,TPM_SESSION **session);
typedef struct extracted_TPM_STORED_DATA12 extracted_TPM_STORED_DATA12;
struct extracted_TPM_STORED_DATA12 {
  UINT32 dataSize;
  BYTE *data;
};
struct extracted_TPM_STORED_DATA12 extract_TPM_STORED_DATA12(TPM_STORED_DATA12 storedData);
TPM_RESULT TPM_OIAP(TPM_SESSION **session);
void write_passphrase(TPM_AUTHDATA nv_auth,TPM_STORED_DATA12 sealedData);
typedef struct TPM_Seal_ret TPM_Seal_ret;
struct TPM_Seal_ret {
  TPM_RESULT returnCode;
  TPM_STORED_DATA12 sealedData;
};
typedef TPM_AUTHDATA TPM_ENCAUTH;
typedef struct tdTPM_PCR_INFO_LONG tdTPM_PCR_INFO_LONG;
typedef BYTE TPM_LOCALITY_SELECTION;
typedef struct tdTPM_PCR_SELECTION tdTPM_PCR_SELECTION;
struct tdTPM_PCR_SELECTION {
  UINT16 sizeOfSelect;

  BYTE *pcrSelect;
};
typedef struct tdTPM_PCR_SELECTION TPM_PCR_SELECTION;
typedef struct tdTPM_DIGEST tdTPM_DIGEST;
struct tdTPM_DIGEST { BYTE digest[0x14]; };
typedef struct tdTPM_DIGEST TPM_DIGEST;
typedef TPM_DIGEST TPM_COMPOSITE_HASH;
struct tdTPM_PCR_INFO_LONG {
  TPM_STRUCTURE_TAG tag;
  TPM_LOCALITY_SELECTION localityAtCreation;
  TPM_LOCALITY_SELECTION localityAtRelease;
  TPM_PCR_SELECTION creationPCRSelection;
  TPM_PCR_SELECTION releasePCRSelection;
  TPM_COMPOSITE_HASH digestAtCreation;
  TPM_COMPOSITE_HASH digestAtRelease;
};
typedef struct tdTPM_PCR_INFO_LONG TPM_PCR_INFO_LONG;
typedef TPM_AUTHDATA TPM_SECRET;
struct TPM_Seal_ret TPM_Seal(TPM_KEY_HANDLE keyHandle_in,TPM_ENCAUTH encAuth_in,TPM_PCR_INFO_LONG pcrInfo_in,const BYTE *inData_in,UINT32 inDataSize_in,TPM_SESSION **session,TPM_SECRET sharedSecret);
TPM_ENCAUTH encAuth_gen(TPM_AUTHDATA entityAuthData,TPM_SECRET sharedSecret,TPM_NONCE authLastNonceEven);
TPM_SECRET sharedSecret_gen(TPM_AUTHDATA auth,TPM_NONCE nonceEvenOSAP,TPM_NONCE nonceOddOSAP);





TPM_RESULT TPM_OSAP(TPM_ENTITY_TYPE entityType_in,UINT32 entityValue_in,TPM_NONCE nonceOddOSAP,TPM_SESSION **session);
TPM_STORED_DATA12 seal_passphrase(TPM_AUTHDATA srk_auth,TPM_AUTHDATA pp_auth,const char *passphrase,UINT32 lenPassphrase);


typedef struct tdTPM_PCR_COMPOSITE tdTPM_PCR_COMPOSITE;
typedef TPM_DIGEST TPM_PCRVALUE;
struct tdTPM_PCR_COMPOSITE {
  TPM_PCR_SELECTION select;
  UINT32 valueSize;

  TPM_PCRVALUE *pcrValue;
};
typedef struct tdTPM_PCR_COMPOSITE TPM_PCR_COMPOSITE;
TPM_COMPOSITE_HASH get_TPM_COMPOSITE_HASH(TPM_PCR_COMPOSITE comp);
# 172 "/Users/scottconstable/Documents/SU_Graduate/SABLE/sable/build/include/sable_verified.h"
const char *tpm_error_to_string(TPM_RESULT res);
void wait(int ms);
void exit(void)__attribute__((noreturn));
# 183 "/Users/scottconstable/Documents/SU_Graduate/SABLE/sable/build/include/sable_verified.h"
typedef struct TPM_PCRRead_ret TPM_PCRRead_ret;
struct TPM_PCRRead_ret {
  TPM_RESULT returnCode;
  TPM_PCRVALUE outDigest;
};
typedef UINT32 TPM_PCRINDEX;
struct TPM_PCRRead_ret TPM_PCRRead(TPM_PCRINDEX pcrIndex_in);
void *alloc(UINT32 size);
TPM_PCR_INFO_LONG get_pcr_info(void);

TPM_NONCE get_nonce(void);
TPM_AUTHDATA get_authdata(void);
typedef struct tdTPM_SEALED_DATA tdTPM_SEALED_DATA;
typedef BYTE TPM_PAYLOAD_TYPE;
struct tdTPM_SEALED_DATA {
  TPM_PAYLOAD_TYPE payload;
  TPM_SECRET authData;
  TPM_SECRET tpmProof;
  TPM_DIGEST storedDigest;
  UINT32 dataSize;

  BYTE *data;
};
typedef struct tdTPM_SEALED_DATA TPM_SEALED_DATA;
# 2 "/Users/scottconstable/Documents/SU_Graduate/SABLE/sable/src/sable_verified.c" 2




typedef TPM_SEALED_DATA
    BOGUS1;

extern TPM_AUTHDATA get_authdata(void);
extern TPM_NONCE get_nonce(void);

static TPM_SESSION *sessions[2] = {0, 0};



TPM_PCR_INFO_LONG get_pcr_info(void) {
  TPM_PCRVALUE *pcr_values = alloc(2 * sizeof(TPM_PCRVALUE));
  BYTE *pcr_select_bytes = alloc(3);
  pcr_select_bytes[0] = 0x00;
  pcr_select_bytes[1] = 0x00;
  pcr_select_bytes[2] = 0x0a;
  TPM_PCR_SELECTION pcr_select = {.sizeOfSelect = 3,
                                  .pcrSelect = (BYTE *)pcr_select_bytes};
  struct TPM_PCRRead_ret pcr17 = TPM_PCRRead(17);
  { if (pcr17.returnCode) { ; exit(); } };
  pcr_values[0] = pcr17.outDigest;
  struct TPM_PCRRead_ret pcr19 = TPM_PCRRead(19);
  { if (pcr19.returnCode) { ; exit(); } };
  pcr_values[1] = pcr19.outDigest;
  TPM_PCR_COMPOSITE composite = {.select = pcr_select,
                                 .valueSize = 2 * sizeof(TPM_PCRVALUE),
                                 .pcrValue = (TPM_PCRVALUE *)pcr_values};
  TPM_COMPOSITE_HASH composite_hash = get_TPM_COMPOSITE_HASH(composite);
  TPM_PCR_INFO_LONG pcr_info = {.tag = ((UINT16)0x0006),
                                .localityAtCreation = (((UINT32)1) << 2),
                                .localityAtRelease = (((UINT32)1) << 2),
                                .creationPCRSelection = pcr_select,
                                .releasePCRSelection = pcr_select,
                                .digestAtCreation = composite_hash,
                                .digestAtRelease = composite_hash};
  return pcr_info;
}

TPM_STORED_DATA12 seal_passphrase(TPM_AUTHDATA srk_auth, TPM_AUTHDATA pp_auth,
                                  const char *passphrase,
                                  UINT32 lenPassphrase) {
  TPM_RESULT res;


  TPM_NONCE nonceOddOSAP = get_nonce();
  res = TPM_OSAP(((UINT16)0x0001), ((UINT32)0x40000000), nonceOddOSAP, &sessions[0]);
  { if (res) { ; exit(); } };
  sessions[0]->nonceOdd = get_nonce();
  sessions[0]->continueAuthSession = 0x00;


  TPM_SECRET sharedSecret =
      sharedSecret_gen(srk_auth, sessions[0]->osap->nonceEvenOSAP,
                       sessions[0]->osap->nonceOddOSAP);


  TPM_ENCAUTH encAuth =
      encAuth_gen(pp_auth, sharedSecret, sessions[0]->nonceEven);

  TPM_PCR_INFO_LONG pcr_info = get_pcr_info();


  struct TPM_Seal_ret seal_ret =
      TPM_Seal(((UINT32)0x40000000), encAuth, pcr_info, (const BYTE *)passphrase,
               lenPassphrase, &sessions[0], sharedSecret);
  { if (seal_ret.returnCode) { ; exit(); } };

  return seal_ret.sealedData;
}

void write_passphrase(TPM_AUTHDATA nv_auth, TPM_STORED_DATA12 sealedData) {
  TPM_RESULT res;

  res = TPM_OIAP(&sessions[0]);
  { if (res) { ; exit(); } };
  sessions[0]->nonceOdd = get_nonce();
  sessions[0]->continueAuthSession = 0x00;

  struct extracted_TPM_STORED_DATA12 x = extract_TPM_STORED_DATA12(sealedData);
  res =
      TPM_NV_WriteValueAuth(x.data, x.dataSize, 0x04, 0, nv_auth, &sessions[0]);
  { if (res) { ; exit(); } };
}

void configure(void) {
  char *passphrase = alloc(128);




  UINT32 lenPassphrase =
      get_string(passphrase, 128 - 1, 1) + 1;


  TPM_AUTHDATA pp_auth = get_authdata();


  TPM_AUTHDATA srk_auth = get_authdata();


  TPM_STORED_DATA12 sealedData =
      seal_passphrase(srk_auth, pp_auth, passphrase, lenPassphrase);



  TPM_AUTHDATA nv_auth = get_authdata();


  write_passphrase(nv_auth, sealedData);
}

TPM_STORED_DATA12 read_passphrase(void) {
  struct TPM_NV_ReadValue_ret val;
  struct TPM_AUTHDATA_option nv_auth;
# 136 "/Users/scottconstable/Documents/SU_Graduate/SABLE/sable/src/sable_verified.c"
  nv_auth.hasValue = 0;
  val = TPM_NV_ReadValue(4, 0, 400, nv_auth, 0);
  { if (val.returnCode) { ; exit(); } };


  return unpack_TPM_STORED_DATA12(val.data, val.dataSize);
}

const char *unseal_passphrase(TPM_AUTHDATA srk_auth, TPM_AUTHDATA pp_auth,
                              TPM_STORED_DATA12 sealed_pp) {
  TPM_RESULT res;

  res = TPM_OIAP(&sessions[0]);
  { if (res) { ; exit(); } };
  sessions[0]->nonceOdd = get_nonce();
  sessions[0]->continueAuthSession = 0x00;

  res = TPM_OIAP(&sessions[1]);
  { if (res) { ; exit(); } };
  sessions[1]->nonceOdd = get_nonce();
  sessions[1]->continueAuthSession = 0x00;

  TPM_Unseal_ret unseal_ret = TPM_Unseal(sealed_pp, ((UINT32)0x40000000), srk_auth,
                                         &sessions[0], pp_auth, &sessions[1]);
  { if (unseal_ret.returnCode) { ; exit(); } };

  return (const char *)unseal_ret.data;
}

void trusted_boot(void) {
  TPM_STORED_DATA12 sealed_pp = read_passphrase();



  TPM_AUTHDATA pp_auth = get_authdata();


  TPM_AUTHDATA srk_auth = get_authdata();

  const char *passphrase = unseal_passphrase(srk_auth, pp_auth, sealed_pp);
# 185 "/Users/scottconstable/Documents/SU_Graduate/SABLE/sable/src/sable_verified.c"
}
