/* adler32.c -- compute the Adler-32 checksum of a data stream
 * Copyright (C) 1995-2011, 2016 Mark Adler
 * For conditions of distribution and use, see copyright notice in zlib.h
 */

/* @(#) $Id$ */

#include "zutil.h"

#define BASE 65521U     /* largest prime smaller than 65536 */
#define NMAX 5552
/* NMAX is the largest n such that 255n(n+1)/2 + (n+1)(BASE-1) <= 2^32-1 */

#define DO1(buf,i)  {adler += (buf)[i]; sum2 += adler;}
#define DO2(buf,i)  DO1(buf,i); DO1(buf,i+1);
#define DO4(buf,i)  DO2(buf,i); DO2(buf,i+2);
#define DO8(buf,i)  DO4(buf,i); DO4(buf,i+4);
#define DO16(buf)   DO8(buf,0); DO8(buf,8);

/* use NO_DIVIDE if your processor does not do division in hardware --
   try it both ways to see which is faster */
#ifdef NO_DIVIDE
/* note that this assumes BASE is 65521, where 65536 % 65521 == 15
   (thank you to John Reiser for pointing this out) */
#  define CHOP(a) \
    do { \
        unsigned long tmp = a >> 16; \
        a &= 0xffffUL; \
        a += (tmp << 4) - tmp; \
    } while (0)
#  define MOD28(a) \
    do { \
        CHOP(a); \
        if (a >= BASE) a -= BASE; \
    } while (0)
#  define MOD(a) \
    do { \
        CHOP(a); \
        MOD28(a); \
    } while (0)
#  define MOD63(a) \
    do { /* this assumes a is not negative */ \
        z_off64_t tmp = a >> 32; \
        a &= 0xffffffffL; \
        a += (tmp << 8) - (tmp << 5) + tmp; \
        tmp = a >> 16; \
        a &= 0xffffL; \
        a += (tmp << 4) - tmp; \
        tmp = a >> 16; \
        a &= 0xffffL; \
        a += (tmp << 4) - tmp; \
        if (a >= BASE) a -= BASE; \
    } while (0)
#else
#  define MOD(a) a %= BASE
#  define MOD28(a) a %= BASE
#  define MOD63(a) a %= BASE
#endif

#if defined(__aarch64__) && defined(__ARM_NEON) && !defined(Z_NO_NEON)
#  include <arm_neon.h>
#  define ADLER32_NEON

/* The most bytes done between reductions: NMAX rounded down to a multiple of
   32. The 16-bit sums per byte position reach at most 173 * 255. */
#define NMAX32 (NMAX & ~31U)

/* Add the len bytes at buf to the sums *adler and *sum2, which are less than
   BASE, and reduce them. len is a multiple of 32, with 0 < len <= NMAX32. */
local void adler32_neon(unsigned long *adler, unsigned long *sum2,
                        const Bytef *buf, unsigned len) {
    static const unsigned short weight[32] = {
        32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17,
        16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1};
    uint32x4_t s1 = vdupq_n_u32(0);     /* sum of the bytes */
    uint32x4_t s2 = vdupq_n_u32(0);     /* sum of s1 before each block */
    uint16x8_t c0 = vdupq_n_u16(0);     /* sums per byte position */
    uint16x8_t c1 = c0, c2 = c0, c3 = c0;
    unsigned n = len;

    do {
        uint8x16_t d0 = vld1q_u8(buf);
        uint8x16_t d1 = vld1q_u8(buf + 16);
        uint16x8_t t;

        s2 = vaddq_u32(s2, s1);
        t = vpaddlq_u8(d0);
        t = vpadalq_u8(t, d1);
        s1 = vpadalq_u16(s1, t);
        c0 = vaddw_u8(c0, vget_low_u8(d0));
        c1 = vaddw_high_u8(c1, d0);
        c2 = vaddw_u8(c2, vget_low_u8(d1));
        c3 = vaddw_high_u8(c3, d1);
        buf += 32;
    } while (n -= 32);

    /* each earlier sum counts for the 32 bytes of its block */
    s2 = vshlq_n_u32(s2, 5);
    s2 = vmlal_u16(s2, vget_low_u16(c0), vld1_u16(weight));
    s2 = vmlal_high_u16(s2, c0, vld1q_u16(weight));
    s2 = vmlal_u16(s2, vget_low_u16(c1), vld1_u16(weight + 8));
    s2 = vmlal_high_u16(s2, c1, vld1q_u16(weight + 8));
    s2 = vmlal_u16(s2, vget_low_u16(c2), vld1_u16(weight + 16));
    s2 = vmlal_high_u16(s2, c2, vld1q_u16(weight + 16));
    s2 = vmlal_u16(s2, vget_low_u16(c3), vld1_u16(weight + 24));
    s2 = vmlal_high_u16(s2, c3, vld1q_u16(weight + 24));

    *sum2 += (unsigned long)len * *adler + vaddvq_u32(s2);
    *adler += vaddvq_u32(s1);
    MOD(*adler);
    MOD(*sum2);
}
#endif

/* ========================================================================= */
uLong ZEXPORT adler32_z(uLong adler, const Bytef *buf, z_size_t len) {
    unsigned long sum2;
    unsigned n;

    /* split Adler-32 into component sums */
    sum2 = (adler >> 16) & 0xffff;
    adler &= 0xffff;

    /* in case user likes doing a byte at a time, keep it fast */
    if (len == 1) {
        adler += buf[0];
        if (adler >= BASE)
            adler -= BASE;
        sum2 += adler;
        if (sum2 >= BASE)
            sum2 -= BASE;
        return adler | (sum2 << 16);
    }

    /* initial Adler-32 value (deferred check for len == 1 speed) */
    if (buf == Z_NULL)
        return 1L;

    /* in case short lengths are provided, keep it somewhat fast */
    if (len < 16) {
        while (len--) {
            adler += *buf++;
            sum2 += adler;
        }
        if (adler >= BASE)
            adler -= BASE;
        MOD28(sum2);            /* only added so many BASE's */
        return adler | (sum2 << 16);
    }

#ifdef ADLER32_NEON
    /* do blocks of 32 bytes, up to NMAX32 bytes at a time */
    while (len >= 32) {
        n = len > NMAX32 ? NMAX32 : (unsigned)len & ~31U;
        adler32_neon(&adler, &sum2, buf, n);
        buf += n;
        len -= n;
    }
#endif

    /* do length NMAX blocks -- requires just one modulo operation */
    while (len >= NMAX) {
        len -= NMAX;
        n = NMAX / 16;          /* NMAX is divisible by 16 */
        do {
            DO16(buf);          /* 16 sums unrolled */
            buf += 16;
        } while (--n);
        MOD(adler);
        MOD(sum2);
    }

    /* do remaining bytes (less than NMAX, still just one modulo) */
    if (len) {                  /* avoid modulos if none remaining */
        while (len >= 16) {
            len -= 16;
            DO16(buf);
            buf += 16;
        }
        while (len--) {
            adler += *buf++;
            sum2 += adler;
        }
        MOD(adler);
        MOD(sum2);
    }

    /* return recombined sums */
    return adler | (sum2 << 16);
}

/* ========================================================================= */
uLong ZEXPORT adler32(uLong adler, const Bytef *buf, uInt len) {
    return adler32_z(adler, buf, len);
}

/* ========================================================================= */
local uLong adler32_combine_(uLong adler1, uLong adler2, z_off64_t len2) {
    unsigned long sum1;
    unsigned long sum2;
    unsigned rem;

    /* for negative len, return invalid adler32 as a clue for debugging */
    if (len2 < 0)
        return 0xffffffffUL;

    /* the derivation of this formula is left as an exercise for the reader */
    MOD63(len2);                /* assumes len2 >= 0 */
    rem = (unsigned)len2;
    sum1 = adler1 & 0xffff;
    sum2 = rem * sum1;
    MOD(sum2);
    sum1 += (adler2 & 0xffff) + BASE - 1;
    sum2 += ((adler1 >> 16) & 0xffff) + ((adler2 >> 16) & 0xffff) + BASE - rem;
    if (sum1 >= BASE) sum1 -= BASE;
    if (sum1 >= BASE) sum1 -= BASE;
    if (sum2 >= ((unsigned long)BASE << 1)) sum2 -= ((unsigned long)BASE << 1);
    if (sum2 >= BASE) sum2 -= BASE;
    return sum1 | (sum2 << 16);
}

/* ========================================================================= */
uLong ZEXPORT adler32_combine(uLong adler1, uLong adler2, z_off_t len2) {
    return adler32_combine_(adler1, adler2, len2);
}

uLong ZEXPORT adler32_combine64(uLong adler1, uLong adler2, z_off64_t len2) {
    return adler32_combine_(adler1, adler2, len2);
}
