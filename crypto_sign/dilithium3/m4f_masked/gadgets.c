/* Copyright SIMPLE-Crypto and PQM4 contributors
 *
 * This file is part of pqm4_masked.
 *
 * pqm4_masked is free software: you can redistribute it and/or modify it under
 * the terms of the GNU General Public License as published by the Free
 * Software Foundation, version 3.
 *
 * pqm4_masked is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for
 * more details.
 *
 * You should have received a copy of the GNU General Public License along with
 * pqm4_masked. If not, see <https://www.gnu.org/licenses/>.
 */
#include "gadgets.h"
#include "masked.h"
#include "masked_representations.h"

static inline uint32_t pini_and_core(uint32_t a, uint32_t b, uint32_t r) {
  uint32_t temp;
  uint32_t s;
  asm("eor %[temp], %[b], %[r]\n\t"
      "and %[temp], %[a], %[temp]\n\t"
      "bic %[s], %[r], %[a]\n\t"
      "eor %[s], %[s], %[temp]"
      : [s] "=r"(s), [temp] "=&r"(temp)    /* outputs, use temp as an
                                              arbitrary-location clobber */
      : [a] "r"(a), [b] "r"(b), [r] "r"(r) /* inputs */
  );
  return s;
}

void masked_xor_c(size_t nshares, uint32_t *out, size_t out_stride,
                  const uint32_t *ina, size_t ina_stride, const uint32_t *inb,
                  size_t inb_stride) {
  for (size_t i = 0; i < nshares; i++) {
    out[i * out_stride] = ina[i * ina_stride] ^ inb[i * inb_stride];
  }
}

void masked_and_c(size_t nshares, uint32_t *z, size_t z_stride,
                  const uint32_t *a, size_t a_stride, const uint32_t *b,
                  size_t b_stride) {
  uint32_t ztmp[nshares];
  uint32_t r;
  uint32_t i, j;

  for (i = 0; i < nshares; i++) {
    ztmp[i] = a[i * a_stride] & b[i * b_stride];
  }

  for (i = 0; i < (nshares - 1); i++) {
    for (j = i + 1; j < nshares; j++) {
      r = get_random();
      // PINI
      ztmp[i] ^= pini_and_core(a[i * a_stride], b[j * b_stride], r);
      ztmp[j] ^= pini_and_core(a[j * a_stride], b[i * b_stride], r);
    }
  }
  for (i = 0; i < nshares; i++) {
    z[i * z_stride] = ztmp[i];
  }
}

/*************************************************
 * Name:        copy_sharing
 *
 * Description: Copy input sharing to output sharing
 *
 * Arguments: - size_t nshares: number of shares
 *            - uint32_t *out: output buffer
 *            - size_t out_stride: out buffer stride
 *            - uint32_t *in: input buffer
 *            - size_t in_stride: in buffer stride
 **************************************************/
void copy_sharing_c(size_t nshares, uint32_t *out, size_t out_stride,
                    const uint32_t *in, size_t in_stride) {
  for (size_t i = 0; i < nshares; i++) {
    out[i * out_stride] = in[i * in_stride];
  }
}

void secadd(size_t nshares, size_t kbits, size_t kbits_out, uint32_t *out,
            size_t out_msk_stride, size_t out_data_stride, const uint32_t *in1,
            size_t in1_msk_stride, size_t in1_data_stride, const uint32_t *in2,
            size_t in2_msk_stride, size_t in2_data_stride) {

  size_t i;
  uint32_t carry[nshares];
  uint32_t xpy[nshares];
  uint32_t xpc[nshares];

  masked_and(nshares, carry, 1, &in1[0 * in1_data_stride], in1_msk_stride,
             &in2[0 * in2_data_stride], in2_msk_stride);

  masked_xor(nshares, &out[0 * out_data_stride], out_msk_stride,
             &in1[0 * in1_data_stride], in1_msk_stride,
             &in2[0 * in2_data_stride], in2_msk_stride);

  for (i = 1; i < kbits; i++) {
    // xpy = in2 ^ in1
    // xpc = in1 ^ carry
    // out = xpy ^ carry

    masked_xor(nshares, xpy, 1, &in1[i * in1_data_stride], in1_msk_stride,
               &in2[i * in2_data_stride], in2_msk_stride);
    masked_xor(nshares, xpc, 1, &in1[i * in1_data_stride], in1_msk_stride,
               carry, 1);
    masked_xor(nshares, &out[i * out_data_stride], out_msk_stride, xpy, 1,
               carry, 1);

    if ((i == (kbits - 1)) && (i == (kbits_out - 1))) {
      break;
    } else if (i == (kbits - 1)) {
      masked_and(nshares, carry, 1, xpy, 1, xpc, 1);
      masked_xor(nshares, &out[(kbits)*out_data_stride], out_msk_stride, carry,
                 1, &in1[i * in1_data_stride], in1_msk_stride);
      break;
    }

    masked_and(nshares, carry, 1, xpy, 1, xpc, 1);
    masked_xor(nshares, carry, 1, carry, 1, &in1[i * in1_data_stride],
               in1_msk_stride);
  }
}

void secadd_constant_bmsk(size_t nshares, size_t kbits, size_t kbits_out,
                          uint32_t *out, size_t out_msk_stride,
                          size_t out_data_stride, const uint32_t *in1,
                          size_t in1_msk_stride, size_t in1_data_stride,
                          uint32_t constant, const uint32_t *bmsk,
                          size_t bmsk_msk_stride) {
  size_t i, d;
  uint32_t carry[nshares];
  uint32_t xpy[nshares];
  uint32_t xpc[nshares];

  if (constant & 0x1) {
    masked_and(nshares, carry, 1, &in1[0 * in1_data_stride], in1_msk_stride,
               bmsk, bmsk_msk_stride);
    masked_xor(nshares, &out[0 * out_data_stride], out_msk_stride,
               &in1[0 * in1_data_stride], in1_msk_stride, bmsk,
               bmsk_msk_stride);
  } else {
    for (d = 0; d < nshares; d++) {
      carry[d] = 0;
    }
    copy_sharing(nshares, out, out_msk_stride, in1, in1_msk_stride);
  }
  for (i = 1; i < kbits; i++) {
    // xpy = in2 ^ in1
    // xpc = in1 ^ carry
    // out = xpy ^ carry
    if ((constant >> i) & 0x1) {
      masked_xor(nshares, xpy, 1, &in1[i * in1_data_stride], in1_msk_stride,
                 bmsk, bmsk_msk_stride);
      masked_xor(nshares, xpc, 1, &in1[i * in1_data_stride], in1_msk_stride,
                 carry, 1);
      masked_xor(nshares, &out[i * out_data_stride], out_msk_stride, xpy, 1,
                 carry, 1);

      if ((i == (kbits - 1)) && (i == (kbits_out - 1))) {
        return;
      } else if (i == (kbits - 1)) {
        masked_and(nshares, carry, 1, xpy, 1, xpc, 1);
        masked_xor(nshares, &out[(kbits)*out_data_stride], out_msk_stride,
                   carry, 1, &in1[i * in1_data_stride], in1_msk_stride);
        return;
      }

      masked_and(nshares, carry, 1, xpy, 1, xpc, 1);
      masked_xor(nshares, carry, 1, carry, 1, &in1[i * in1_data_stride],
                 in1_msk_stride);
    } else {
      // compute the carry
      masked_xor(nshares, &out[i * out_data_stride], out_msk_stride, carry, 1,
                 &in1[i * in1_data_stride], in1_msk_stride);

      if ((i == (kbits - 1)) && (i == (kbits_out - 1))) {
        return;
      } else if (i == (kbits - 1)) {
        masked_and(nshares, &out[(kbits)*out_data_stride], out_msk_stride,
                   carry, 1, &in1[i * in1_data_stride], in1_msk_stride);
        return;
      }
      masked_and(nshares, carry, 1, carry, 1, &in1[i * in1_data_stride],
                 in1_msk_stride);
    }
  }
}

void secadd_constant(size_t nshares, size_t kbits, size_t kbits_out,
                     uint32_t *out, size_t out_msk_stride,
                     size_t out_data_stride, const uint32_t *in1,
                     size_t in1_msk_stride, size_t in1_data_stride,
                     uint32_t constant) {

  size_t i, d;
  uint32_t carry[nshares];
  uint32_t xpy[nshares];
  uint32_t xpc[nshares];
  uint32_t dummy = 0;

  if (constant & 0x1) {
    copy_sharing(nshares, carry, 1, in1, in1_msk_stride);
    copy_sharing(nshares, out, out_msk_stride, in1, in1_msk_stride);
    secxor_cst(out, 0xFFFFFFFF, &dummy);
  } else {
    for (d = 0; d < nshares; d++) {
      carry[d] = 0;
    }
    copy_sharing(nshares, out, out_msk_stride, in1, in1_msk_stride);
  }

  for (i = 1; i < kbits; i++) {
    if ((constant >> i) & 0x1) {
      copy_sharing(nshares, xpy, 1, &in1[i * in1_data_stride], in1_msk_stride);
      masked_xor(nshares, xpc, 1, &in1[i * in1_data_stride], in1_msk_stride,
                 carry, 1);
      masked_xor(nshares, &out[i * out_data_stride], out_msk_stride, xpy, 1,
                 carry, 1);

      secxor_cst(xpy, 0xFFFFFFFF, &dummy);
      secxor_cst(out + i * out_data_stride, 0xFFFFFFFF, &dummy);

      if ((i == (kbits - 1)) && (i == (kbits_out - 1))) {
        return;
      } else if (i == (kbits - 1)) {
        masked_and(nshares, carry, 1, xpy, 1, xpc, 1);
        masked_xor(nshares, &out[(kbits)*out_data_stride], out_msk_stride,
                   carry, 1, &in1[i * in1_data_stride], in1_msk_stride);

        // add the kbits_out of the constant
        secxor_cst(out + kbits * out_data_stride,
                   0xFFFFFFFF * ((constant >> kbits) & 0x1), &dummy);

        return;
      }

      masked_and(nshares, carry, 1, xpy, 1, xpc, 1);
      masked_xor(nshares, carry, 1, carry, 1, &in1[i * in1_data_stride],
                 in1_msk_stride);
    } else {
      // compute the carry
      masked_xor(nshares, &out[i * out_data_stride], out_msk_stride, carry, 1,
                 &in1[i * in1_data_stride], in1_msk_stride);

      if ((i == (kbits - 1)) && (i == (kbits_out - 1))) {
        return;
      } else if (i == (kbits - 1)) {
        masked_and(nshares, &out[(kbits)*out_data_stride], out_msk_stride,
                   carry, 1, &in1[i * in1_data_stride], in1_msk_stride);

        // add the kbits_out of the constant
        secxor_cst(out + kbits * out_data_stride,
                   0xFFFFFFFF * ((constant >> kbits) & 0x1), &dummy);
        return;
      }
      masked_and(nshares, carry, 1, carry, 1, &in1[i * in1_data_stride],
                 in1_msk_stride);
    }
  }
}

void refresh_pair_c(uint32_t *x, uint32_t *y) {
  uint32_t r = get_random();
  *x ^= r;
  *y ^= r;
}

void refresh_pair_asm(uint32_t *x, uint32_t *y) {
  uint32_t temp, dummy;
  asm("bl get_random\n\t"
      "ldr %[temp], [%[x]]\n\t"
      "eor %[temp], %[temp], r0\n\t"
      "str %[temp], [%[x]]\n\t"
      "ldr %[temp], [%[y]]\n\t"
      "eor %[temp], %[temp], r0\n\t"
      "str %[temp], [%[y]]\n\t"
      "ldr %[temp], [%[dummy]]\n\t"
      "str %[temp], [%[dummy]]\n\t"
      "mov r0, #0\n\t"
      : /* outputs, use temp as an arbitrary-location clobber */
      [temp] "=&r"(temp)
      : /* inputs */
      [x] "r"(x), [y] "r"(y), [dummy] "r"(&dummy)
      : /* clobbers */
      "r0");
}

void sec_zero_sh_rec(size_t nshares, uint32_t *x) {
  if (nshares == 1) {
    x[0] = 0;
  } else if (nshares == 2) {
    x[0] = 0;
    x[1] = 0;
    refresh_pair(x, x + 1);
  } else {
    sec_zero_sh_rec(nshares / 2, x);
    sec_zero_sh_rec(nshares - (nshares / 2), x + nshares / 2);
    for (unsigned int i = 0; i < nshares / 2; i++) {
      refresh_pair(x + i, x + i + nshares / 2);
    }
  }
}

/*************************************************
 * Name:        refreshIOS
 *
 * Description: IOS refresh on boolean sharing
 *
 * Arguments:
 *            - uint32_t *x: input buffer
 *            - size_t x_msk_stride: stride between shares
 **************************************************/
void refreshIOS(uint32_t *x, size_t x_msk_stride) {
  uint32_t sh0[NSHARES];
  sec_zero_sh_rec(NSHARES, &sh0[0]);
  masked_xor(NSHARES, x, x_msk_stride, x, x_msk_stride, sh0, 1);
}

// Takes a masked array of size 32, output 1 iff all the values are less than or
// equal to the bound 'constant'
uint32_t secleq_constant(size_t kbits, const uint32_t *in, size_t in_msk_stride,
                         size_t in_data_stride, uint32_t constant) {
  uint32_t add_res[NSHARES * (kbits + 1)];
  uint32_t unmasked_bit;

  secadd_constant(NSHARES, kbits, kbits + 1, add_res, 1, NSHARES, in,
                  in_msk_stride, in_data_stride,
                  (1 << (kbits + 1)) - constant - 1);
  for (size_t k = 0; k < kbits + 1; k++) {
    refreshIOS(add_res, 1);
  }
  unmasked_bit = add_res[kbits * NSHARES];
  for (size_t d = 1; d < NSHARES; d++) {
    unmasked_bit ^= add_res[kbits * NSHARES + d];
  }
  return unmasked_bit == 0xffffffff;
}

/*************************************************
 * Name:        secadd_modp
 *
 * Description: Performs masked addition of two bitslice words with
 *              arbitrary modulo such that
 *              out = (in1 + in2)%(p)
 *
 * Arguments: - size_t nshares: number of shares
 *            - size_t kbits: number of bits in input words:
 *                requires kbits = ceil(log(p))
 *            - uint32_t: modulo for the reduction
 *            - uint32_t *out: output buffer
 *            - size_t out_msk_stride: stride between shares
 *            - size_t out_data_stride: stride between masked bits
 *            - uint32_t *in1: first input buffer
 *            - size_t in1_msk_stride: stride between shares
 *            - size_t in1_data_stride: stride between masked bits
 *            - uint32_t *in2: second input buffer
 *            - size_t in2_msk_stride: stride between shares
 *            - size_t in2_data_stride: stride between masked bits
 **************************************************/
void secadd_modp(size_t nshares, size_t kbits, uint32_t q, uint32_t *out,
                 size_t out_msk_stride, size_t out_data_stride,
                 const uint32_t *in1, size_t in1_msk_stride,
                 size_t in1_data_stride, const uint32_t *in2,
                 size_t in2_msk_stride, size_t in2_data_stride) {

  uint32_t s[(kbits + 1) * nshares];
  uint32_t sp[(kbits + 1) * nshares];

  secadd(nshares, kbits, kbits + 1, s, 1, nshares, in1, in1_msk_stride,
         in1_data_stride, in2, in2_msk_stride, in2_data_stride);
  secadd_constant(nshares, kbits + 1, kbits + 1, sp, 1, nshares, s, 1, nshares,
                  (1 << (kbits + 1)) - q);
  secadd_constant_bmsk(nshares, kbits, kbits, out, out_msk_stride,
                       out_data_stride, sp, 1, nshares, q, &sp[kbits * nshares],
                       1);
}
