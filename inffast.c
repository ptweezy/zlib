/* inffast.c -- fast decoding
 * Copyright (C) 1995-2026 Mark Adler
 * For conditions of distribution and use, see copyright notice in zlib.h
 */

#include "zutil.h"
#include "inftrees.h"
#include "inflate.h"
#include "inffast.h"

#ifdef ASMINF
#  pragma message("Assembler code may have bugs -- use at your own risk")
#else

#ifdef Z_U8
/* Fast loop: with a 64-bit type the bit buffer is refilled eight bytes at a
   time, and matches are copied eight or sixteen bytes at a time. */

#define TRACE_LITERAL(here) \
    Tracevv((stderr, (here)->val >= 0x20 && (here)->val < 0x7f ? \
            "inflate:         literal '%c'\n" : \
            "inflate:         literal 0x%02x\n", (here)->val))

/* The eight bytes at p, little-endian: one load on a little-endian machine,
   the bytes one by one otherwise. */
local Z_U8 load64(z_const unsigned char FAR *p) {
    Z_U8 v = 1;

    if (*(unsigned char *)&v) {
        zmemcpy(&v, p, 8);
        return v;
    }
    return (Z_U8)p[0] | ((Z_U8)p[1] << 8) | ((Z_U8)p[2] << 16) |
           ((Z_U8)p[3] << 24) | ((Z_U8)p[4] << 32) | ((Z_U8)p[5] << 40) |
           ((Z_U8)p[6] << 48) | ((Z_U8)p[7] << 56);
}

/* Fill hold8 to at least 56 bits from the eight bytes at in. Bits above the
   count in bits may already be there from an earlier refill; they are the same
   bits, so adding them again changes nothing. */
#define REFILL8() \
    do { \
        hold8 |= load64(in) << bits; \
        in += (63 - bits) >> 3; \
        bits |= 56; \
    } while (0)

/* The extra bits of entry e, from the bit buffer as it was before the code
   and its extra bits were dropped: the low e.bits bits without the code. */
#define EXTRA8(old, e) \
    ((unsigned)(((old) & (((Z_U8)1 << (e).bits) - 1)) >> ((e).op & 15)))

/* A table entry as one word: bits in the low byte, then op, then val in the
   high half. One load on a little-endian machine. */
local unsigned entry8(code const FAR *p) {
    Z_U8 v = 1;
    unsigned w;

    if (*(unsigned char *)&v && sizeof(w) == sizeof(*p)) {
        zmemcpy(&w, p, sizeof(w));
        return w;
    }
    return (unsigned)p->bits | ((unsigned)p->op << 8) |
           ((unsigned)p->val << 16);
}

/* The extra bits of entry word w, from the bit buffer as it was before the
   code and its extra bits were dropped. */
#define EXTRAW(old, w) \
    ((unsigned)(((old) & (((Z_U8)1 << ((w) & 63)) - 1)) >> (((w) >> 8) & 15)))

/* Make the compiler compute x here, and not later where it is used. */
#if defined(__GNUC__) || defined(__clang__)
#  define KEEP8(x) __asm__ __volatile__("" : "+r"(x))
#else
#  define KEEP8(x) (void)(x)
#endif

/* copy_back() may write up to this many bytes after the end of a match. */
#define FAST8_SLOP 31

/* Output room the fast loop needs between two checks: the three literals it
   may write. The room for a match is checked when its length is known. */
#define FAST8_OUT 3

/* A table entry word with this bit set came from a second-level table, so
   that the bits of its first-level entry were dropped as well. */
#define FAST8_SUB 0x8000U

/* Copy len >= 1 bytes from dist bytes back in the output to out, and return
   out + len. It may write up to FAST8_SLOP bytes after out + len, so the
   caller must have that room. The first two steps are done without a test, so
   that the usual short match needs no loop. */
local unsigned char FAR *copy_back(unsigned char FAR *out, unsigned dist,
                                   unsigned len) {
    unsigned char FAR *from = out - dist;
    unsigned char FAR *stop = out + len;

    if (dist >= 16) {                   /* sixteen at a time, no overlap */
        zmemcpy(out, from, 16);
        zmemcpy(out + 16, from + 16, 16);
        if (len > 32) {
            out += 32;
            from += 32;
            do {
                zmemcpy(out, from, 16);
                out += 16;
                from += 16;
            } while (out < stop);
        }
        return stop;
    }
    if (dist >= 8) {                    /* eight at a time, no overlap */
        zmemcpy(out, from, 8);
        zmemcpy(out + 8, from + 8, 8);
        if (len > 16) {
            out += 16;
            from += 16;
            do {
                zmemcpy(out, from, 8);
                out += 8;
                from += 8;
            } while (out < stop);
        }
        return stop;
    }
    if (dist == 1) {                    /* a run of one byte, eight at a time */
        Z_U8 run = *from;
        run |= run << 8;
        run |= run << 16;
        run |= run << 32;
        do {
            zmemcpy(out, &run, 8);
            out += 8;
        } while (out < stop);
        return stop;
    }
    /* dist 2..7: eight bytes per step, of which the first dist are right;
       the next step rewrites the rest */
    do {
        Z_U8 v;
        zmemcpy(&v, from, 8);
        zmemcpy(out, &v, 8);
        out += dist;
        from += dist;
    } while (out < stop);
    return stop;
}
#endif

/*
   Decode literal, length, and distance codes and write out the resulting
   literal and match bytes until either not enough input or output is
   available, an end-of-block is encountered, or a data error is encountered.
   When large enough input and output buffers are supplied to inflate(), for
   example, a 16K input buffer and a 64K output buffer, more than 95% of the
   inflate execution time is spent in this routine.

   Entry assumptions:

        state->mode == LEN
        strm->avail_in >= 6
        start >= strm->avail_out
        state->bits < 8

   On return, state->mode is one of:

        LEN -- ran out of enough available input
        LIT -- decoded a literal that there is no room for: state->length
               is the literal, and state->back is set for it
        MATCH -- decoded a length/distance pair that there is no room to
                 copy here: state->length, state->offset, state->was and
                 state->back are set for it, and nothing of it was copied
        TYPE -- reached end of block code, inflate() to interpret next block
        BAD -- error in block data

   Notes:

    - The maximum input bits used by a length/distance pair is 15 bits for the
      length code, 5 bits for the length extra, 15 bits for the distance code,
      and 13 bits for the distance extra.  This totals 48 bits, or six bytes.
      Therefore if strm->avail_in >= 6, then there is enough input to avoid
      checking for available input while decoding.

    - The room for a literal or a match is checked when it has been
      decoded.  One that does not fit is left to the caller in the LIT or
      MATCH state: for a match the caller copies what fits, and the rest on
      later calls.  So when the output is full, the next code has been
      decoded as well, as inflate() does when it decodes the codes itself.
 */
void ZLIB_INTERNAL inflate_fast(z_streamp strm, unsigned start) {
    struct inflate_state FAR *state;
    z_const unsigned char FAR *in;      /* local strm->next_in */
    z_const unsigned char FAR *last;    /* have enough input while in < last */
    unsigned char FAR *out;     /* local strm->next_out */
    unsigned char FAR *beg;     /* inflate()'s initial strm->next_out */
    unsigned char FAR *end;     /* end of the available output */
#ifdef INFLATE_STRICT
    unsigned dmax;              /* maximum distance from zlib header */
#endif
    unsigned wsize;             /* window size or zero if not using window */
    unsigned whave;             /* valid bytes in the window */
    unsigned wnext;             /* window write index */
    unsigned char FAR *window;  /* allocated sliding window, if wsize != 0 */
    unsigned long hold;         /* local strm->hold */
    unsigned bits;              /* local strm->bits */
    code const FAR *lcode;      /* local strm->lencode */
    code const FAR *dcode;      /* local strm->distcode */
    unsigned lmask;             /* mask for first level of length codes */
    unsigned dmask;             /* mask for first level of distance codes */
    code const *here;           /* retrieved table entry */
    unsigned op;                /* code bits, operation, extra bits, or */
                                /*  window position, window bytes to copy */
    unsigned len;               /* match length, unused bytes */
    unsigned dist;              /* match distance */
    unsigned mark;              /* unread input bits when a code starts */
    unsigned char FAR *from;    /* where to copy match from */
#ifdef Z_U8
    Z_U8 hold8;                 /* 64-bit bit buffer of the fast loop */
    Z_U8 old8;                  /* hold8 before the last code was dropped */
    unsigned e;                 /* literal/length table entry, as a word */
    unsigned d;                 /* distance table entry, as a word */
    unsigned nl, nd;            /* the entries that may come next */
    unsigned ne;                /* the entry after the distance code nd */
    unsigned nl2, nd2;          /* the entries that may follow literal nl */
    z_const unsigned char FAR *last8;   /* three refills fit after in */
    unsigned char FAR *end8;    /* room for FAST8_OUT bytes after out */
    unsigned char FAR *near8;   /* check the room for a match from here on */
    unsigned char FAR *stop8;   /* end of a match copied sixteen at a time */
    unsigned wd;                /* distance back in the window */
    unsigned seg;               /* bytes from there to the end of the piece */
    unsigned wmask;             /* all ones if the match starts in the window */
    unsigned pmask;             /* all ones if in the older piece of it */
    unsigned sw;                /* all ones for a simple copy from the window */
    unsigned simple;            /* not zero to copy sixteen bytes at a time */
    unsigned char FAR *base[2]; /* start of the output, and the window */
#endif

    /* copy state to local variables */
    state = (struct inflate_state FAR *)strm->state;
    in = strm->next_in;
    last = in + (strm->avail_in - 5);
    out = strm->next_out;
    beg = out - (start - strm->avail_out);
    end = out + strm->avail_out;
#ifdef INFLATE_STRICT
    dmax = state->dmax;
#endif
    wsize = state->wsize;
    whave = state->whave;
    wnext = state->wnext;
    window = state->window;
    hold = state->hold;
    bits = state->bits;
    lcode = state->lencode;
    dcode = state->distcode;
    lmask = (1U << state->lenbits) - 1;
    dmask = (1U << state->distbits) - 1;

#ifdef Z_U8
    /* Fast loop. It runs while 24 bytes can be read at in (three refills of
       eight bytes, each advancing in by up to seven) and the output
       has room for FAST8_OUT bytes: between two checks the loop writes at
       most three literals, or two literals and then a match. The room for
       a match is checked when its length is known: copy_back() may write
       FAST8_SLOP bytes past the match, so a match that ends closer than
       that to the end of the output is copied byte by byte.

       Table entries are words here: bits in the low byte, op above it, val
       in the high half. Each table lookup uses only bits that are already in
       hold8, and a refill follows the lookup, so the refill does not delay
       the lookup. The first-level entry for the next code is looked up
       before a match is copied. Each code starts with at least 56 bits in
       hold8. Two literals, a length code and its extra bits take at most 40
       of them, which leaves enough for the first-level distance lookup. */
    if (strm->avail_in >= 24 && strm->avail_out >= FAST8_OUT) {
        last8 = in + (strm->avail_in - 24);
        end8 = out + (strm->avail_out - FAST8_OUT);
        near8 = strm->avail_out > 258 + FAST8_SLOP ?
                end - (258 + FAST8_SLOP) : out;
        base[0] = beg;
        base[1] = window;
        hold8 = hold;
        REFILL8();
        e = entry8(lcode + (hold8 & lmask));
        for (;;) {
            old8 = hold8;
            hold8 >>= e & 63;
            bits -= e & 0xff;
            nl = entry8(lcode + (hold8 & lmask));
            nd = entry8(dcode + (hold8 & dmask));
            ne = entry8(lcode + ((hold8 >> (nd & 63)) & lmask));
            nl2 = entry8(lcode + ((hold8 >> (nl & 63)) & lmask));
            nd2 = entry8(dcode + ((hold8 >> (nl & 63)) & dmask));
            KEEP8(nl);
            KEEP8(nd);
            KEEP8(ne);
            KEEP8(nl2);
            KEEP8(nd2);
            if ((e & 0x7f00) == 0) {    /* up to three literals */
                *out++ = (unsigned char)(e >> 16);
                e = nl;
                old8 = hold8;
                hold8 >>= e & 63;
                bits -= e & 0xff;
                nl = nl2;
                nd = nd2;
                ne = entry8(lcode + ((hold8 >> (nd & 63)) & lmask));
                KEEP8(nl);
                KEEP8(nd);
                KEEP8(ne);
                if ((e & 0x7f00) == 0) {
                    *out++ = (unsigned char)(e >> 16);
                    e = nl;
                  dolen8:
                    old8 = hold8;
                    hold8 >>= e & 63;
                    bits -= e & 0xff;
                    nd = entry8(dcode + (hold8 & dmask));
                    ne = entry8(lcode + ((hold8 >> (nd & 63)) & lmask));
                    KEEP8(nd);
                    KEEP8(ne);
                    if ((e & 0x7f00) == 0) {
                        *out++ = (unsigned char)(e >> 16);
                        if (in > last8 || out > end8)
                            break;
                        e = entry8(lcode + (hold8 & lmask));
                        REFILL8();
                        continue;
                    }
                }
            }
            if (e & 0x1000) {           /* length base */
                len = (e >> 16) + EXTRAW(old8, e);
                Tracevv((stderr, "inflate:         length %u\n", len));
                d = nd;
                if (bits < 15 + 13 + 10) {
                    REFILL8();
                    ne = entry8(lcode + ((hold8 >> (d & 63)) & lmask));
                }
              dodist8:
                old8 = hold8;
                hold8 >>= d & 63;
                bits -= d & 0xff;
                if (d & 0x1000) {       /* distance base */
                    dist = (d >> 16) + EXTRAW(old8, d);
#ifdef INFLATE_STRICT
                    if (dist > dmax) {
                        strm->msg = (z_const char *)
                            "invalid distance too far back";
                        state->mode = BAD;
                        break;
                    }
#endif
                    Tracevv((stderr, "inflate:         distance %u\n", dist));

                    if (out >= near8 &&
                        (unsigned)(end - out) < len + FAST8_SLOP) {
                        /* near the end of the output: copy byte by byte */
                        op = (unsigned)(out - beg);
                        op = dist > op ? dist - op : 0; /* bytes in window */
                        if (len > (unsigned)(end - out) || op > whave) {
                            /* no room for the match, or its distance is
                               too far back: leave it to inflate(), with the
                               bits of its codes for inflateMark() */
                            state->mode = MATCH;
                            state->length = len;
                            state->was = len;
                            state->offset = dist;
                            state->back = (int)((e & 0xff) + (d & 0xff) +
                                (e & FAST8_SUB ? state->lenbits : 0) +
                                (d & FAST8_SUB ? state->distbits : 0));
                            break;
                        }
                        e = entry8(lcode + (hold8 & lmask));
                        REFILL8();
                        if (op) {               /* some from the window */
                            from = window + (op > wnext ? wsize + wnext - op :
                                                          wnext - op);
                            if (op > len)
                                op = len;
                            len -= op;
                            do {
                                *out++ = *from++;
                                if (from == window + wsize)
                                    from = window;
                            } while (--op);
                        }
                        if (len) {              /* the rest from the output */
                            from = out - dist;
                            do {
                                *out++ = *from++;
                            } while (--len);
                        }
                        goto copied8;
                    }

                    /* the next code was looked up already; refill now,
                       before the match is copied */
                    e = ne;
                    REFILL8();

                    op = (unsigned)(out - beg); /* max distance in output */
                    if (op >= 32768U) {
                        /* no distance is longer: all from the output */
                        simple = dist >= 16;
                        from = out - dist;
                    }
                    else {
                        /* The match may start in the window. With a small
                           output buffer the processor cannot predict that,
                           so the usual match is set up without a branch on
                           it, using masks: sixteen bytes at a time from the
                           output, or from one piece of the window that has
                           FAST8_SLOP bytes after the match. The window has
                           two pieces: the newer wnext bytes at its start,
                           and before those the bytes up to its end. */
                        wmask = 0U - (unsigned)(dist > op);
                        wd = dist - op;
                        pmask = 0U - (unsigned)(wd > wnext);
                        seg = wd - (wnext & pmask);
                        sw = wmask & (0U - (unsigned)(wd <= whave)) &
                             (0U - (unsigned)(seg >= len + FAST8_SLOP));
                        simple = sw | (~wmask & (unsigned)(dist >= 16));
                        /* the source, counted from the start of the window
                           or of the output; the start of the output itself
                           if the match is in the window and not simple */
                        from = base[sw & 1] +
                               ((sw & (wnext + (wsize & pmask) - wd)) |
                                (~wmask & (op - dist)));
                    }
                    if (simple) {
                        stop8 = out + len;
                        zmemcpy(out, from, 16);
                        zmemcpy(out + 16, from + 16, 16);
                        if (len > 32) {
                            out += 32;
                            from += 32;
                            do {
                                zmemcpy(out, from, 16);
                                out += 16;
                                from += 16;
                            } while (out < stop8);
                        }
                        out = stop8;
                    }
                    else if (dist > op) {       /* the rest from the window */
                        op = dist - op;         /* distance back in window */
                        if (op > whave) {
                            if (state->sane) {
                                strm->msg = (z_const char *)
                                    "invalid distance too far back";
                                state->mode = BAD;
                                break;
                            }
#ifdef INFLATE_ALLOW_INVALID_DISTANCE_TOOFAR_ARRR
                            if (len <= op - whave) {
                                do {
                                    *out++ = 0;
                                } while (--len);
                                goto copied8;
                            }
                            len -= op - whave;
                            do {
                                *out++ = 0;
                            } while (--op > whave);
                            if (op == 0) {
                                out = copy_back(out, dist, len);
                                goto copied8;
                            }
#endif
                        }
                        from = window;
                        if (wnext == 0)         /* very common case */
                            from += wsize - op;
                        else if (wnext < op) {  /* wrap around window */
                            from += wsize + wnext - op;
                            op -= wnext;
                            if (op < len) {     /* end of window, then start */
                                zmemcpy(out, from, op);
                                out += op;
                                len -= op;
                                from = window;
                                op = wnext;
                            }
                        }
                        else                    /* contiguous in window */
                            from += wnext - op;
                        if (len + 15 <= op) {
                            /* all from the window, which has enough bytes
                               after the match to read sixteen at a time */
                            stop8 = out + len;
                            do {
                                zmemcpy(out, from, 16);
                                out += 16;
                                from += 16;
                            } while (out < stop8);
                            out = stop8;
                        }
                        else {
                            if (op > len)
                                op = len;
                            zmemcpy(out, from, op); /* from the window */
                            out += op;
                            len -= op;
                            if (len)                /* rest from output */
                                out = copy_back(out, dist, len);
                        }
                    }
                    else                        /* a short distance */
                        out = copy_back(out, dist, len);
                  copied8:
                    if (in > last8 || out > end8)
                        break;
                    continue;
                }
                else if ((d & 0x4000) == 0) {   /* 2nd level distance code */
                    d = entry8(dcode + (d >> 16) +
                               (hold8 & ((1U << ((d >> 8) & 15)) - 1))) |
                        FAST8_SUB;
                    ne = entry8(lcode + ((hold8 >> (d & 63)) & lmask));
                    goto dodist8;
                }
                else {
                    strm->msg = (z_const char *)"invalid distance code";
                    state->mode = BAD;
                    break;
                }
            }
            else if ((e & 0x4000) == 0) {       /* 2nd level length code */
                e = entry8(lcode + (e >> 16) +
                           (hold8 & ((1U << ((e >> 8) & 15)) - 1))) | FAST8_SUB;
                goto dolen8;
            }
            else if (e & 0x2000) {              /* end-of-block */
                Tracevv((stderr, "inflate:         end of block\n"));
                state->mode = TYPE;
                break;
            }
            else {
                strm->msg = (z_const char *)"invalid literal/length code";
                state->mode = BAD;
                break;
            }
        }

        /* return the whole bytes not used, leaving fewer than eight bits */
        len = bits >> 3;
        in -= len;
        bits -= len << 3;
        hold = (unsigned long)(hold8 & ((1U << bits) - 1));
        if (state->mode != LEN || in >= last)
            goto leave;
    }
#endif

    /* decode literals and length/distances until end-of-block or not enough
       input data or output space */
    do {
        mark = (((unsigned)(last - in) << 3) + bits);
        if (bits < 15) {
            hold += (unsigned long)(*in++) << bits;
            bits += 8;
            hold += (unsigned long)(*in++) << bits;
            bits += 8;
        }
        here = lcode + (hold & lmask);
      dolen:
        op = (unsigned)(here->op);
        len = CODE_BITS(*here);
        hold >>= len;
        bits -= len;
        if (op == 0) {                          /* literal */
            Tracevv((stderr, here->val >= 0x20 && here->val < 0x7f ?
                    "inflate:         literal '%c'\n" :
                    "inflate:         literal 0x%02x\n", here->val));
            if (out == end) {
                /* no room for the literal: leave it to inflate(), with
                   the bits of its code for inflateMark() */
                state->mode = LIT;
                state->length = (unsigned)(here->val);
                state->back = (int)(mark - (((unsigned)(last - in) << 3) +
                                            bits));
                break;
            }
            *out++ = (unsigned char)(here->val);
        }
        else if (op & 16) {                     /* length base */
            op = (unsigned)(here->bits) - len;  /* number of extra bits */
            len = (unsigned)(here->val);
            if (op) {
                if (bits < op) {
                    hold += (unsigned long)(*in++) << bits;
                    bits += 8;
                }
                len += (unsigned)hold & ((1U << op) - 1);
                hold >>= op;
                bits -= op;
            }
            Tracevv((stderr, "inflate:         length %u\n", len));
            if (bits < 15) {
                hold += (unsigned long)(*in++) << bits;
                bits += 8;
                hold += (unsigned long)(*in++) << bits;
                bits += 8;
            }
            here = dcode + (hold & dmask);
          dodist:
            op = (unsigned)(here->op);
            dist = CODE_BITS(*here);
            hold >>= dist;
            bits -= dist;
            if (op & 16) {                      /* distance base */
                op = (unsigned)(here->bits) - dist; /* number of extra bits */
                dist = (unsigned)(here->val);
                if (bits < op) {
                    hold += (unsigned long)(*in++) << bits;
                    bits += 8;
                    if (bits < op) {
                        hold += (unsigned long)(*in++) << bits;
                        bits += 8;
                    }
                }
                dist += (unsigned)hold & ((1U << op) - 1);
#ifdef INFLATE_STRICT
                if (dist > dmax) {
                    strm->msg = (z_const char *)
                        "invalid distance too far back";
                    state->mode = BAD;
                    break;
                }
#endif
                hold >>= op;
                bits -= op;
                Tracevv((stderr, "inflate:         distance %u\n", dist));
                if (len > (unsigned)(end - out)) {
                    /* no room for the match: leave it to inflate(), with
                       the bits of its codes for inflateMark() */
                    state->mode = MATCH;
                    state->length = len;
                    state->was = len;
                    state->offset = dist;
                    state->back = (int)(mark - (((unsigned)(last - in) << 3) + bits));
                    break;
                }
                op = (unsigned)(out - beg);     /* max distance in output */
                if (dist > op) {                /* see if copy from window */
                    op = dist - op;             /* distance back in window */
                    if (op > whave) {
                        if (state->sane) {
                            strm->msg = (z_const char *)
                                "invalid distance too far back";
                            state->mode = BAD;
                            break;
                        }
#ifdef INFLATE_ALLOW_INVALID_DISTANCE_TOOFAR_ARRR
                        if (len <= op - whave) {
                            do {
                                *out++ = 0;
                            } while (--len);
                            continue;
                        }
                        len -= op - whave;
                        do {
                            *out++ = 0;
                        } while (--op > whave);
                        if (op == 0) {
                            from = out - dist;
                            do {
                                *out++ = *from++;
                            } while (--len);
                            continue;
                        }
#endif
                    }
                    from = window;
                    if (wnext == 0) {           /* very common case */
                        from += wsize - op;
                        if (op < len) {         /* some from window */
                            len -= op;
                            do {
                                *out++ = *from++;
                            } while (--op);
                            from = out - dist;  /* rest from output */
                        }
                    }
                    else if (wnext < op) {      /* wrap around window */
                        from += wsize + wnext - op;
                        op -= wnext;
                        if (op < len) {         /* some from end of window */
                            len -= op;
                            do {
                                *out++ = *from++;
                            } while (--op);
                            from = window;
                            if (wnext < len) {  /* some from start of window */
                                op = wnext;
                                len -= op;
                                do {
                                    *out++ = *from++;
                                } while (--op);
                                from = out - dist;      /* rest from output */
                            }
                        }
                    }
                    else {                      /* contiguous in window */
                        from += wnext - op;
                        if (op < len) {         /* some from window */
                            len -= op;
                            do {
                                *out++ = *from++;
                            } while (--op);
                            from = out - dist;  /* rest from output */
                        }
                    }
                    while (len > 2) {
                        *out++ = *from++;
                        *out++ = *from++;
                        *out++ = *from++;
                        len -= 3;
                    }
                    if (len) {
                        *out++ = *from++;
                        if (len > 1)
                            *out++ = *from++;
                    }
                }
                else {
                    from = out - dist;          /* copy direct from output */
                    do {                        /* minimum length is three */
                        *out++ = *from++;
                        *out++ = *from++;
                        *out++ = *from++;
                        len -= 3;
                    } while (len > 2);
                    if (len) {
                        *out++ = *from++;
                        if (len > 1)
                            *out++ = *from++;
                    }
                }
            }
            else if ((op & 64) == 0) {          /* 2nd level distance code */
                here = dcode + here->val + (hold & ((1U << op) - 1));
                goto dodist;
            }
            else {
                strm->msg = (z_const char *)"invalid distance code";
                state->mode = BAD;
                break;
            }
        }
        else if ((op & 64) == 0) {              /* 2nd level length code */
            here = lcode + here->val + (hold & ((1U << op) - 1));
            goto dolen;
        }
        else if (op & 32) {                     /* end-of-block */
            Tracevv((stderr, "inflate:         end of block\n"));
            state->mode = TYPE;
            break;
        }
        else {
            strm->msg = (z_const char *)"invalid literal/length code";
            state->mode = BAD;
            break;
        }
    } while (in < last);

#ifdef Z_U8
  leave:
#endif
    /* return unused bytes (on entry, bits < 8, so in won't go too far back) */
    len = bits >> 3;
    in -= len;
    bits -= len << 3;
    hold &= (1U << bits) - 1;

    /* update state and return */
    strm->next_in = in;
    strm->next_out = out;
    strm->avail_in = (unsigned)(in < last ? 5 + (last - in) : 5 - (in - last));
    strm->avail_out = (unsigned)(end - out);
    state->hold = hold;
    state->bits = bits;
    return;
}

/*
   inflate_fast() speedups that turned out slower (on a PowerPC G3 750CXe):
   - Using bit fields for code structure
   - Different op definition to avoid & for extra bits (do & for table bits)
   - Three separate decoding do-loops for direct, window, and wnext == 0
   - Special case for distance > 1 copies to do overlapped load and store copy
   - Explicit branch predictions (based on measured branch probabilities)
   - Deferring match copy and interspersed it with decoding subsequent codes
   - Swapping literal/length else
   - Swapping window/direct else
   - Larger unrolled copy loops (three is about right)
   - Moving len -= 3 statement into middle of loop
 */

#endif /* !ASMINF */
