---
layout: post
title:  "Arithmetic in the Rijndael field"
date:   2018-04-11 18:09:09 +0000
---

This is a short note-to-self about doing arithmetic in a finite field of order
2<sup>8</sup> as I can never remember exactly how it works, and have spent time
computing the necessary tables at least twice before and don't want to do it
again.

Fields of order 2<sup>8</sup> are useful for places where you want to work with
bytes as if they were more like proper numbers, and particularly when you want
to have a sensible notion of what it means to divide one byte by another. This
includes things like

- [AES (a.k.a. Rijndael)](https://en.wikipedia.org/wiki/Advanced_Encryption_Standard)
- [Shamir's secret-sharing algorithm](https://en.wikipedia.org/wiki/Shamir%27s_Secret_Sharing)
- [Reed-Solomon coding](https://en.wikipedia.org/wiki/Reed–Solomon_error_correction)

The integers mod a prime _p_ form a finite field _F<sub>p</sub>_ of order _p_.
A finite field with order _p<sup>n</sup>_ is constructed by taking the quotient
of the ring of polynomials _F<sub>p</sub>[x]_ by a primitive polynomial of
order _n_. _F<sub>p</sub>[x]_ comprises polynomials in _x_ with coefficients in
_F<sub>p</sub>_, and primitive polynomials are ones that have no proper
factors.

Here _p_ is 2, so the base field _F<sub>2</sub>_ has just 2 elements, _0_ and
_1_, in which addition is XOR and multiplication is AND.  The nonprimitive
polynomials of order 8 can be found by taking the products of all nonconstant
polynomials _P_ and _Q_ whose orders sum to 8, and the primitive polynomials
are whatever is left, which are the following:

Code    |    x<sup>8</sup> |  + x<sup>7</sup> |  + x<sup>6</sup> |  + x<sup>5</sup> |  + x<sup>4</sup> |  + x<sup>3</sup> |  + x<sup>2</sup> |              + x |              + 1
--------|------------------|------------------|------------------|------------------|------------------|------------------|------------------|------------------|------------------
0x011b  |    x<sup>8</sup> |                  |                  |                  |  + x<sup>4</sup> |  + x<sup>3</sup> |                  |              + x |              + 1
0x011d  |    x<sup>8</sup> |                  |                  |                  |  + x<sup>4</sup> |  + x<sup>3</sup> |  + x<sup>2</sup> |                  |              + 1
0x012b  |    x<sup>8</sup> |                  |                  |  + x<sup>5</sup> |                  |  + x<sup>3</sup> |                  |              + x |              + 1
0x012d  |    x<sup>8</sup> |                  |                  |  + x<sup>5</sup> |                  |  + x<sup>3</sup> |  + x<sup>2</sup> |                  |              + 1
0x0139  |    x<sup>8</sup> |                  |                  |  + x<sup>5</sup> |  + x<sup>4</sup> |  + x<sup>3</sup> |                  |                  |              + 1
0x013f  |    x<sup>8</sup> |                  |                  |  + x<sup>5</sup> |  + x<sup>4</sup> |  + x<sup>3</sup> |  + x<sup>2</sup> |              + x |              + 1
0x014d  |    x<sup>8</sup> |                  |  + x<sup>6</sup> |                  |                  |  + x<sup>3</sup> |  + x<sup>2</sup> |                  |              + 1
0x015f  |    x<sup>8</sup> |                  |  + x<sup>6</sup> |                  |  + x<sup>4</sup> |  + x<sup>3</sup> |  + x<sup>2</sup> |              + x |              + 1
0x0163  |    x<sup>8</sup> |                  |  + x<sup>6</sup> |  + x<sup>5</sup> |                  |                  |                  |              + x |              + 1
0x0165  |    x<sup>8</sup> |                  |  + x<sup>6</sup> |  + x<sup>5</sup> |                  |                  |  + x<sup>2</sup> |                  |              + 1
0x0169  |    x<sup>8</sup> |                  |  + x<sup>6</sup> |  + x<sup>5</sup> |                  |  + x<sup>3</sup> |                  |                  |              + 1
0x0171  |    x<sup>8</sup> |                  |  + x<sup>6</sup> |  + x<sup>5</sup> |  + x<sup>4</sup> |                  |                  |                  |              + 1
0x0177  |    x<sup>8</sup> |                  |  + x<sup>6</sup> |  + x<sup>5</sup> |  + x<sup>4</sup> |                  |  + x<sup>2</sup> |              + x |              + 1
0x017b  |    x<sup>8</sup> |                  |  + x<sup>6</sup> |  + x<sup>5</sup> |  + x<sup>4</sup> |  + x<sup>3</sup> |                  |              + x |              + 1
0x0187  |    x<sup>8</sup> |  + x<sup>7</sup> |                  |                  |                  |                  |  + x<sup>2</sup> |              + x |              + 1
0x018b  |    x<sup>8</sup> |  + x<sup>7</sup> |                  |                  |                  |  + x<sup>3</sup> |                  |              + x |              + 1
0x018d  |    x<sup>8</sup> |  + x<sup>7</sup> |                  |                  |                  |  + x<sup>3</sup> |  + x<sup>2</sup> |                  |              + 1
0x019f  |    x<sup>8</sup> |  + x<sup>7</sup> |                  |                  |  + x<sup>4</sup> |  + x<sup>3</sup> |  + x<sup>2</sup> |              + x |              + 1
0x01a3  |    x<sup>8</sup> |  + x<sup>7</sup> |                  |  + x<sup>5</sup> |                  |                  |                  |              + x |              + 1
0x01a9  |    x<sup>8</sup> |  + x<sup>7</sup> |                  |  + x<sup>5</sup> |                  |  + x<sup>3</sup> |                  |                  |              + 1
0x01b1  |    x<sup>8</sup> |  + x<sup>7</sup> |                  |  + x<sup>5</sup> |  + x<sup>4</sup> |                  |                  |                  |              + 1
0x01bd  |    x<sup>8</sup> |  + x<sup>7</sup> |                  |  + x<sup>5</sup> |  + x<sup>4</sup> |  + x<sup>3</sup> |  + x<sup>2</sup> |                  |              + 1
0x01c3  |    x<sup>8</sup> |  + x<sup>7</sup> |  + x<sup>6</sup> |                  |                  |                  |                  |              + x |              + 1
0x01cf  |    x<sup>8</sup> |  + x<sup>7</sup> |  + x<sup>6</sup> |                  |                  |  + x<sup>3</sup> |  + x<sup>2</sup> |              + x |              + 1
0x01d7  |    x<sup>8</sup> |  + x<sup>7</sup> |  + x<sup>6</sup> |                  |  + x<sup>4</sup> |                  |  + x<sup>2</sup> |              + x |              + 1
0x01dd  |    x<sup>8</sup> |  + x<sup>7</sup> |  + x<sup>6</sup> |                  |  + x<sup>4</sup> |  + x<sup>3</sup> |  + x<sup>2</sup> |                  |              + 1
0x01e7  |    x<sup>8</sup> |  + x<sup>7</sup> |  + x<sup>6</sup> |  + x<sup>5</sup> |                  |                  |  + x<sup>2</sup> |              + x |              + 1
0x01f3  |    x<sup>8</sup> |  + x<sup>7</sup> |  + x<sup>6</sup> |  + x<sup>5</sup> |  + x<sup>4</sup> |                  |                  |              + x |              + 1
0x01f5  |    x<sup>8</sup> |  + x<sup>7</sup> |  + x<sup>6</sup> |  + x<sup>5</sup> |  + x<sup>4</sup> |                  |  + x<sup>2</sup> |                  |              + 1
0x01f9  |    x<sup>8</sup> |  + x<sup>7</sup> |  + x<sup>6</sup> |  + x<sup>5</sup> |  + x<sup>4</sup> |  + x<sup>3</sup> |                  |                  |              + 1

[Rijndael's finite
field](https://en.wikipedia.org/wiki/Finite_field_arithmetic#Rijndael%27s_finite_field)
uses the quotient of _F<sub>2</sub>[x]_ by the first of these, x<sup>8</sup> +
x<sup>4</sup> + x<sup>3</sup> + x + 1.

Each element of the Rijndael field is an equivalence class of polynomials, one
of which, _P_, has degree less than 8, and the bit pattern _B(P)_ of the
coefficients of that representative maps the Rijndael field onto the values
that a byte can take. Addition of elements corresponds simply to XOR of the
corresponding bytes. Multiplication is more involved, but a good way to work is
by calculating a log table and its inverse, and then adding logs instead of
trying to multiply the bytes directly.

Not all bases are suitable for taking logs here, because some elements' powers
do not hit every other element. For instance, _x<sup>51</sup>_ = 1, so _x_ is
not a suitable base. The simplest suitable base is _x+1_, because no power of
_x+1_ below 255 equals 1. Fortunately, it's quite simple to compute the product
of an arbitrary element by _x+1_ in terms of their bit patterns:

> _B((x+1)P) = B(P) XOR (B(P) ≪ 1) XOR (CARRY ? 0x1b : 0x00)_

Here _CARRY_ corresponds to the most-significant bit of _B(P)_, which is lost
when calculating _B(P) ≪ 1_ but which is equivalent to _0x1b_ because
x<sup>8</sup> = x<sup>4</sup> + x<sup>3</sup> + x + 1 according to the
quotient, and _B(x<sup>4</sup> + x<sup>3</sup> + x + 1) = 0x1b_.

Working entirely with the bit patterns, the powers of _B(x+1)_ are as follows:

 `__`  | `_0` | `_1` | `_2` | `_3` | `_4` | `_5` | `_6` | `_7` | `_8` | `_9` | `_a` | `_b` | `_c` | `_d` | `_e` | `_f`
-------|------|------|------|------|------|------|------|------|------|------|------|------|------|------|------|-----
 `0_`  | `01` | `03` | `05` | `0f` | `11` | `33` | `55` | `ff` | `1a` | `2e` | `72` | `96` | `a1` | `f8` | `13` | `35`
 `1_`  | `5f` | `e1` | `38` | `48` | `d8` | `73` | `95` | `a4` | `f7` | `02` | `06` | `0a` | `1e` | `22` | `66` | `aa`
 `2_`  | `e5` | `34` | `5c` | `e4` | `37` | `59` | `eb` | `26` | `6a` | `be` | `d9` | `70` | `90` | `ab` | `e6` | `31`
 `3_`  | `53` | `f5` | `04` | `0c` | `14` | `3c` | `44` | `cc` | `4f` | `d1` | `68` | `b8` | `d3` | `6e` | `b2` | `cd`
 `4_`  | `4c` | `d4` | `67` | `a9` | `e0` | `3b` | `4d` | `d7` | `62` | `a6` | `f1` | `08` | `18` | `28` | `78` | `88`
 `5_`  | `83` | `9e` | `b9` | `d0` | `6b` | `bd` | `dc` | `7f` | `81` | `98` | `b3` | `ce` | `49` | `db` | `76` | `9a`
 `6_`  | `b5` | `c4` | `57` | `f9` | `10` | `30` | `50` | `f0` | `0b` | `1d` | `27` | `69` | `bb` | `d6` | `61` | `a3`
 `7_`  | `fe` | `19` | `2b` | `7d` | `87` | `92` | `ad` | `ec` | `2f` | `71` | `93` | `ae` | `e9` | `20` | `60` | `a0`
 `8_`  | `fb` | `16` | `3a` | `4e` | `d2` | `6d` | `b7` | `c2` | `5d` | `e7` | `32` | `56` | `fa` | `15` | `3f` | `41`
 `9_`  | `c3` | `5e` | `e2` | `3d` | `47` | `c9` | `40` | `c0` | `5b` | `ed` | `2c` | `74` | `9c` | `bf` | `da` | `75`
 `a_`  | `9f` | `ba` | `d5` | `64` | `ac` | `ef` | `2a` | `7e` | `82` | `9d` | `bc` | `df` | `7a` | `8e` | `89` | `80`
 `b_`  | `9b` | `b6` | `c1` | `58` | `e8` | `23` | `65` | `af` | `ea` | `25` | `6f` | `b1` | `c8` | `43` | `c5` | `54`
 `c_`  | `fc` | `1f` | `21` | `63` | `a5` | `f4` | `07` | `09` | `1b` | `2d` | `77` | `99` | `b0` | `cb` | `46` | `ca`
 `d_`  | `45` | `cf` | `4a` | `de` | `79` | `8b` | `86` | `91` | `a8` | `e3` | `3e` | `42` | `c6` | `51` | `f3` | `0e`
 `e_`  | `12` | `36` | `5a` | `ee` | `29` | `7b` | `8d` | `8c` | `8f` | `8a` | `85` | `94` | `a7` | `f2` | `0d` | `17`
 `f_`  | `39` | `4b` | `dd` | `7c` | `84` | `97` | `a2` | `fd` | `1c` | `24` | `6c` | `b4` | `c7` | `52` | `f6` | `--`
{: .java-type-table }

The inverse of this table is the log table to use when performing
multiplications:

 `__`  | `_0` | `_1` | `_2` | `_3` | `_4` | `_5` | `_6` | `_7` | `_8` | `_9` | `_a` | `_b` | `_c` | `_d` | `_e` | `_f`
-------|------|------|------|------|------|------|------|------|------|------|------|------|------|------|------|-----
 `0_`  | `--` | `00` | `19` | `01` | `32` | `02` | `1a` | `c6` | `4b` | `c7` | `1b` | `68` | `33` | `ee` | `df` | `03`
 `1_`  | `64` | `04` | `e0` | `0e` | `34` | `8d` | `81` | `ef` | `4c` | `71` | `08` | `c8` | `f8` | `69` | `1c` | `c1`
 `2_`  | `7d` | `c2` | `1d` | `b5` | `f9` | `b9` | `27` | `6a` | `4d` | `e4` | `a6` | `72` | `9a` | `c9` | `09` | `78`
 `3_`  | `65` | `2f` | `8a` | `05` | `21` | `0f` | `e1` | `24` | `12` | `f0` | `82` | `45` | `35` | `93` | `da` | `8e`
 `4_`  | `96` | `8f` | `db` | `bd` | `36` | `d0` | `ce` | `94` | `13` | `5c` | `d2` | `f1` | `40` | `46` | `83` | `38`
 `5_`  | `66` | `dd` | `fd` | `30` | `bf` | `06` | `8b` | `62` | `b3` | `25` | `e2` | `98` | `22` | `88` | `91` | `10`
 `6_`  | `7e` | `6e` | `48` | `c3` | `a3` | `b6` | `1e` | `42` | `3a` | `6b` | `28` | `54` | `fa` | `85` | `3d` | `ba`
 `7_`  | `2b` | `79` | `0a` | `15` | `9b` | `9f` | `5e` | `ca` | `4e` | `d4` | `ac` | `e5` | `f3` | `73` | `a7` | `57`
 `8_`  | `af` | `58` | `a8` | `50` | `f4` | `ea` | `d6` | `74` | `4f` | `ae` | `e9` | `d5` | `e7` | `e6` | `ad` | `e8`
 `9_`  | `2c` | `d7` | `75` | `7a` | `eb` | `16` | `0b` | `f5` | `59` | `cb` | `5f` | `b0` | `9c` | `a9` | `51` | `a0`
 `a_`  | `7f` | `0c` | `f6` | `6f` | `17` | `c4` | `49` | `ec` | `d8` | `43` | `1f` | `2d` | `a4` | `76` | `7b` | `b7`
 `b_`  | `cc` | `bb` | `3e` | `5a` | `fb` | `60` | `b1` | `86` | `3b` | `52` | `a1` | `6c` | `aa` | `55` | `29` | `9d`
 `c_`  | `97` | `b2` | `87` | `90` | `61` | `be` | `dc` | `fc` | `bc` | `95` | `cf` | `cd` | `37` | `3f` | `5b` | `d1`
 `d_`  | `53` | `39` | `84` | `3c` | `41` | `a2` | `6d` | `47` | `14` | `2a` | `9e` | `5d` | `56` | `f2` | `d3` | `ab`
 `e_`  | `44` | `11` | `92` | `d9` | `23` | `20` | `2e` | `89` | `b4` | `7c` | `b8` | `26` | `77` | `99` | `e3` | `a5`
 `f_`  | `67` | `4a` | `ed` | `de` | `c5` | `31` | `fe` | `18` | `0d` | `63` | `8c` | `80` | `c0` | `f7` | `70` | `07`
{: .java-type-table }

Here are the same tables in an easier-to-copy-and-paste format.

Powers of _x+1_:

    0x01, 0x03, 0x05, 0x0f, 0x11, 0x33, 0x55, 0xff, 0x1a, 0x2e, 0x72, 0x96, 0xa1,
    0xf8, 0x13, 0x35, 0x5f, 0xe1, 0x38, 0x48, 0xd8, 0x73, 0x95, 0xa4, 0xf7, 0x02,
    0x06, 0x0a, 0x1e, 0x22, 0x66, 0xaa, 0xe5, 0x34, 0x5c, 0xe4, 0x37, 0x59, 0xeb,
    0x26, 0x6a, 0xbe, 0xd9, 0x70, 0x90, 0xab, 0xe6, 0x31, 0x53, 0xf5, 0x04, 0x0c,
    0x14, 0x3c, 0x44, 0xcc, 0x4f, 0xd1, 0x68, 0xb8, 0xd3, 0x6e, 0xb2, 0xcd, 0x4c,
    0xd4, 0x67, 0xa9, 0xe0, 0x3b, 0x4d, 0xd7, 0x62, 0xa6, 0xf1, 0x08, 0x18, 0x28,
    0x78, 0x88, 0x83, 0x9e, 0xb9, 0xd0, 0x6b, 0xbd, 0xdc, 0x7f, 0x81, 0x98, 0xb3,
    0xce, 0x49, 0xdb, 0x76, 0x9a, 0xb5, 0xc4, 0x57, 0xf9, 0x10, 0x30, 0x50, 0xf0,
    0x0b, 0x1d, 0x27, 0x69, 0xbb, 0xd6, 0x61, 0xa3, 0xfe, 0x19, 0x2b, 0x7d, 0x87,
    0x92, 0xad, 0xec, 0x2f, 0x71, 0x93, 0xae, 0xe9, 0x20, 0x60, 0xa0, 0xfb, 0x16,
    0x3a, 0x4e, 0xd2, 0x6d, 0xb7, 0xc2, 0x5d, 0xe7, 0x32, 0x56, 0xfa, 0x15, 0x3f,
    0x41, 0xc3, 0x5e, 0xe2, 0x3d, 0x47, 0xc9, 0x40, 0xc0, 0x5b, 0xed, 0x2c, 0x74,
    0x9c, 0xbf, 0xda, 0x75, 0x9f, 0xba, 0xd5, 0x64, 0xac, 0xef, 0x2a, 0x7e, 0x82,
    0x9d, 0xbc, 0xdf, 0x7a, 0x8e, 0x89, 0x80, 0x9b, 0xb6, 0xc1, 0x58, 0xe8, 0x23,
    0x65, 0xaf, 0xea, 0x25, 0x6f, 0xb1, 0xc8, 0x43, 0xc5, 0x54, 0xfc, 0x1f, 0x21,
    0x63, 0xa5, 0xf4, 0x07, 0x09, 0x1b, 0x2d, 0x77, 0x99, 0xb0, 0xcb, 0x46, 0xca,
    0x45, 0xcf, 0x4a, 0xde, 0x79, 0x8b, 0x86, 0x91, 0xa8, 0xe3, 0x3e, 0x42, 0xc6,
    0x51, 0xf3, 0x0e, 0x12, 0x36, 0x5a, 0xee, 0x29, 0x7b, 0x8d, 0x8c, 0x8f, 0x8a,
    0x85, 0x94, 0xa7, 0xf2, 0x0d, 0x17, 0x39, 0x4b, 0xdd, 0x7c, 0x84, 0x97, 0xa2,
    0xfd, 0x1c, 0x24, 0x6c, 0xb4, 0xc7, 0x52, 0xf6

Logs base _x+1_:
     
    0x00, 0x19, 0x01, 0x32, 0x02, 0x1a, 0xc6, 0x4b, 0xc7, 0x1b, 0x68, 0x33, 0xee,
    0xdf, 0x03, 0x64, 0x04, 0xe0, 0x0e, 0x34, 0x8d, 0x81, 0xef, 0x4c, 0x71, 0x08,
    0xc8, 0xf8, 0x69, 0x1c, 0xc1, 0x7d, 0xc2, 0x1d, 0xb5, 0xf9, 0xb9, 0x27, 0x6a,
    0x4d, 0xe4, 0xa6, 0x72, 0x9a, 0xc9, 0x09, 0x78, 0x65, 0x2f, 0x8a, 0x05, 0x21,
    0x0f, 0xe1, 0x24, 0x12, 0xf0, 0x82, 0x45, 0x35, 0x93, 0xda, 0x8e, 0x96, 0x8f,
    0xdb, 0xbd, 0x36, 0xd0, 0xce, 0x94, 0x13, 0x5c, 0xd2, 0xf1, 0x40, 0x46, 0x83,
    0x38, 0x66, 0xdd, 0xfd, 0x30, 0xbf, 0x06, 0x8b, 0x62, 0xb3, 0x25, 0xe2, 0x98,
    0x22, 0x88, 0x91, 0x10, 0x7e, 0x6e, 0x48, 0xc3, 0xa3, 0xb6, 0x1e, 0x42, 0x3a,
    0x6b, 0x28, 0x54, 0xfa, 0x85, 0x3d, 0xba, 0x2b, 0x79, 0x0a, 0x15, 0x9b, 0x9f,
    0x5e, 0xca, 0x4e, 0xd4, 0xac, 0xe5, 0xf3, 0x73, 0xa7, 0x57, 0xaf, 0x58, 0xa8,
    0x50, 0xf4, 0xea, 0xd6, 0x74, 0x4f, 0xae, 0xe9, 0xd5, 0xe7, 0xe6, 0xad, 0xe8,
    0x2c, 0xd7, 0x75, 0x7a, 0xeb, 0x16, 0x0b, 0xf5, 0x59, 0xcb, 0x5f, 0xb0, 0x9c,
    0xa9, 0x51, 0xa0, 0x7f, 0x0c, 0xf6, 0x6f, 0x17, 0xc4, 0x49, 0xec, 0xd8, 0x43,
    0x1f, 0x2d, 0xa4, 0x76, 0x7b, 0xb7, 0xcc, 0xbb, 0x3e, 0x5a, 0xfb, 0x60, 0xb1,
    0x86, 0x3b, 0x52, 0xa1, 0x6c, 0xaa, 0x55, 0x29, 0x9d, 0x97, 0xb2, 0x87, 0x90,
    0x61, 0xbe, 0xdc, 0xfc, 0xbc, 0x95, 0xcf, 0xcd, 0x37, 0x3f, 0x5b, 0xd1, 0x53,
    0x39, 0x84, 0x3c, 0x41, 0xa2, 0x6d, 0x47, 0x14, 0x2a, 0x9e, 0x5d, 0x56, 0xf2,
    0xd3, 0xab, 0x44, 0x11, 0x92, 0xd9, 0x23, 0x20, 0x2e, 0x89, 0xb4, 0x7c, 0xb8,
    0x26, 0x77, 0x99, 0xe3, 0xa5, 0x67, 0x4a, 0xed, 0xde, 0xc5, 0x31, 0xfe, 0x18,
    0x0d, 0x63, 0x8c, 0x80, 0xc0, 0xf7, 0x70, 0x07 
