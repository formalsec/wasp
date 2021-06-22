#include "stdlib.h"
#include "assert.h"

#define SIZE_MAX 100000

#define IMPLIES(a, b) (!(a) || (b))
#define AWS_PRECONDITION(cond) assert(cond)
#define AWS_POSTCONDITION(cond) assert(cond)

#define AWS_MEM_IS_READABLE(base, len) (((len) == 0) || (base))
#define AWS_MEM_IS_WRITABLE(base, len) (((len) == 0) || (base))
#define AWS_OBJECT_PTR_IS_READABLE(ptr) AWS_MEM_IS_READABLE((ptr), sizeof(*(ptr)))
#define AWS_OBJECT_PTR_IS_WRITABLE(ptr) AWS_MEM_IS_WRITABLE((ptr), sizeof(*(ptr)))

#define AWS_ATOMIC_VAR_PTRVAL(var) ((var)->value)

typedef size_t aws_atomic_impl_int_t;

#define AWS_ATOMIC_VAR_INTVAL(var) (*(aws_atomic_impl_int_t *)(var))

typedef unsigned int  bool;
typedef unsigned char uint8_t;
typedef unsigned long uint64_t;

struct aws_atomic_var {
    void *value;
};

struct aws_cryptosdk_cmm {
    struct aws_atomic_var refcount;
    const struct aws_cryptosdk_cmm_vt *vtable;
};

enum aws_cryptosdk_alg_id {
    ALG_AES256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384 = 0x0578,
    ALG_AES256_GCM_HKDF_SHA512_COMMIT_KEY            = 0x0478,
    ALG_AES256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 = 0x0378,
    ALG_AES192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 = 0x0346,
    ALG_AES128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256 = 0x0214,
    ALG_AES256_GCM_IV12_TAG16_HKDF_SHA256            = 0x0178,
    ALG_AES192_GCM_IV12_TAG16_HKDF_SHA256            = 0x0146,
    ALG_AES128_GCM_IV12_TAG16_HKDF_SHA256            = 0x0114,
    ALG_AES256_GCM_IV12_TAG16_NO_KDF                 = 0x0078,
    ALG_AES192_GCM_IV12_TAG16_NO_KDF                 = 0x0046,
    ALG_AES128_GCM_IV12_TAG16_NO_KDF                 = 0x0014
};

enum aws_cryptosdk_commitment_policy {
    /**
     * Algorithm suite must support key commitment. Key commitment will be
     * included in ciphertext on encrypt. Valid key commitment must be present
     * in ciphertext on decrypt.
     */
    COMMITMENT_POLICY_REQUIRE_ENCRYPT_REQUIRE_DECRYPT = 0x598f396c,

    /**
     * Algorithm suite must support key commitment. Key commitment will be
     * included in ciphertext on encrypt. On decrypt, if a key commitment is
     * present on the ciphertext, then the key commitment must be valid.
     */
    COMMITMENT_POLICY_REQUIRE_ENCRYPT_ALLOW_DECRYPT = 0x493769b7,

    /**
     * Algorithm suite must NOT support key commitment. Key commitment will NOT
     * be included in ciphertext on encrypt. On decrypt, if a key commitment is
     * present on the ciphertext, then the key commitment must be valid.
     */
    COMMITMENT_POLICY_FORBID_ENCRYPT_ALLOW_DECRYPT = 0x2735f98a,
};

struct aws_cryptosdk_enc_request {
    struct aws_allocator *alloc;
    /**
     * The encryption context for this message. CMMs are permitted to modify this
     * hash table in order to inject additional keys or otherwise modify the encryption
     * context.
     */
    struct aws_hash_table *enc_ctx;
    /**
     * The session will initially call generate_enc_materials on the CMM
     * with a zero requested_alg; it's up to one of the CMMs in the chain to fill
     * this in before the keyring is invoked. In particular, the default CMM will
     * fill in the algorithm ID it has been configured with, unless a CMM before
     * the default CMM filled in a different algorithm ID.
     */
    enum aws_cryptosdk_alg_id requested_alg;
    /**
     * An upper-bound on the plaintext size to be encrypted (comes from @ref
     * aws_cryptosdk_session_set_message_bound or @ref
     * aws_cryptosdk_session_set_message_size). If no bound has been set,
     * this will be UINT64_MAX.
     */
    uint64_t plaintext_size;
    /**
     * The key commitment policy to enforce when processing the encryption
     * request. The CMM is responsible for selecting an algorithm that
     * satisfies the commitment policy: if the commitment policy requires key
     * commitment, then the algorithm must be a key-committing one; otherwise,
     * the algorithm must NOT be a key-committing one.
     */
    enum aws_cryptosdk_commitment_policy commitment_policy;
};

struct aws_byte_buf {
    /* do not reorder this, this struct lines up nicely with windows buffer structures--saving us allocations.*/
    size_t len;
    uint8_t *buffer;
    size_t capacity;
    struct aws_allocator *allocator;
};

struct aws_array_list {
    struct aws_allocator *alloc;
    size_t current_size;
    size_t length;
    size_t item_size;
    void *data;
};

struct aws_cryptosdk_enc_materials {
    struct aws_allocator *alloc;
    struct aws_byte_buf unencrypted_data_key;
    /** Contains a trace of which wrapping keys took which actions in this request */
    struct aws_array_list keyring_trace;
    /** List of struct aws_cryptosdk_edk objects */
    struct aws_array_list encrypted_data_keys;
    /** Trailing signature context, or NULL if no trailing signature is needed for this algorithm */
    struct aws_cryptosdk_sig_ctx *signctx;
    enum aws_cryptosdk_alg_id alg;
};

struct aws_cryptosdk_dec_materials {
    struct aws_allocator *alloc;
    struct aws_byte_buf unencrypted_data_key;
    /** Contains a trace of which wrapping keys took which actions in this request */
    struct aws_array_list keyring_trace;
    /** Trailing signature context, or NULL if no trailing signature is needed for this algorithm */
    struct aws_cryptosdk_sig_ctx *signctx;
    enum aws_cryptosdk_alg_id alg;
};

struct aws_cryptosdk_dec_request {
    struct aws_allocator *alloc;
    const struct aws_hash_table *enc_ctx;
    struct aws_array_list encrypted_data_keys;
    enum aws_cryptosdk_alg_id alg;
};

struct aws_cryptosdk_cmm_vt {
    /**
     * Always set to sizeof(struct aws_cryptosdk_cmm_vt).
     */
    size_t vt_size;
    /**
     * Identifier for debugging purposes only.
     */
    const char *name;
    /**
     * VIRTUAL FUNCTION: must implement unless it is a no-op. It is better to implement it as
     * a no-op function to avoid setting error code.
     */
    void (*destroy)(struct aws_cryptosdk_cmm *cmm);

    /**
     * VIRTUAL FUNCTION: must implement if used for encryption.
     */
    int (*generate_enc_materials)(
        struct aws_cryptosdk_cmm *cmm,
        struct aws_cryptosdk_enc_materials **output,
        struct aws_cryptosdk_enc_request *request);
    /**
     * VIRTUAL FUNCTION: must implement if used for decryption.
     */
    int (*decrypt_materials)(
        struct aws_cryptosdk_cmm *cmm,
        struct aws_cryptosdk_dec_materials **output,
        struct aws_cryptosdk_dec_request *request);
};

bool aws_c_string_is_valid(const char *str) {
    /* Knowing the actual length to check would require strlen(), which is
     * a) linear time in the length of the string
     * b) could already cause a memory violation for a non-zero-terminated string.
     * But we know that a c-string must have at least one character, to store the null terminator
     */
    return str && AWS_MEM_IS_READABLE(str, 1);
}

bool aws_cryptosdk_cmm_vtable_is_valid(const struct aws_cryptosdk_cmm_vt *vtable) {
    return AWS_OBJECT_PTR_IS_READABLE(vtable) && vtable->vt_size == sizeof(struct aws_cryptosdk_cmm_vt) &&
           aws_c_string_is_valid(vtable->name);
}

bool aws_atomic_var_is_valid_int(const struct aws_atomic_var *var) {
    return AWS_MEM_IS_WRITABLE(var, sizeof(size_t));
}
/*
 * For sequential proofs, we directly access the atomic value,
 * so we can correctly propagate it through CBMC assumptions.
 */
size_t aws_atomic_load_int(const struct aws_atomic_var *var) {
    return *((size_t *)(var));
}

bool aws_cryptosdk_cmm_base_is_valid(const struct aws_cryptosdk_cmm *cmm) {
    return AWS_OBJECT_PTR_IS_WRITABLE(cmm) && aws_atomic_var_is_valid_int(&cmm->refcount) &&
           aws_atomic_load_int(&cmm->refcount) > 0 && aws_atomic_load_int(&cmm->refcount) <= SIZE_MAX &&
           aws_cryptosdk_cmm_vtable_is_valid(cmm->vtable);
}

void aws_atomic_init_int(volatile struct aws_atomic_var *var, size_t n) {
    AWS_ATOMIC_VAR_INTVAL(var) = n;
}

void aws_cryptosdk_cmm_base_init(
    struct aws_cryptosdk_cmm *cmm, const struct aws_cryptosdk_cmm_vt *vtable) {
    AWS_PRECONDITION(AWS_OBJECT_PTR_IS_WRITABLE(cmm));
    AWS_PRECONDITION(aws_cryptosdk_cmm_vtable_is_valid(vtable));
    cmm->vtable = vtable;
    aws_atomic_init_int(&cmm->refcount, 1);
    AWS_POSTCONDITION(aws_cryptosdk_cmm_base_is_valid(cmm));
}

const char *ensure_c_str_is_allocated(size_t max_size) {
    size_t cap = __VERIFIER_nondet_int("cap");
    assume(cap > 0 && cap <= max_size);
    const char *str = malloc(cap);
    char *s = (char *) str;
    for (int i = 0; i < cap - 1; ++i) {
      char sym_char = __VERIFIER_nondet_char("str[i]");
      if (sym_char == '\0') sym_char++;
      s[i] = sym_char;
    }
    s[cap-1] = '\0';
    /* Ensure that its a valid c string. Since all bytes are nondeterminstic, the actual
     * string length is 0..str_cap
     */
    assume(IMPLIES(str != NULL, str[cap - 1] == '\0'));
    return str;
}

void ensure_nondet_allocate_cmm_vtable_members(struct aws_cryptosdk_cmm_vt *vtable, size_t max_len) {
    if (vtable) {
        vtable->vt_size = sizeof(struct aws_cryptosdk_cmm_vt);
        vtable->name = ensure_c_str_is_allocated(max_len);
    }
}

int main() {
    /* Nondet input */
    struct aws_cryptosdk_cmm cmm;
    struct aws_cryptosdk_cmm_vt vtable;

    /* Assumptions */
    ensure_nondet_allocate_cmm_vtable_members(&vtable, SIZE_MAX);
    assume(aws_cryptosdk_cmm_vtable_is_valid(&vtable));

    /* Operation under verification */
    aws_cryptosdk_cmm_base_init(&cmm, &vtable);

    /* Post-conditions */
    assert(aws_cryptosdk_cmm_base_is_valid(&cmm));
    return 0;
}
