# Palprime counts

`palprime_counts.csv` lists, for each base b from 2 to 16 and each odd digit length L with b^L < 1.8·10¹⁹:

| column | meaning |
|---|---|
| `base` | the base b |
| `digits` | the length L in base b (odd; for even L the only palprime is b + 1 when b + 1 is prime and L = 2) |
| `palindromes` | number of base-b palindromes with exactly L digits, (b − 1)·b^((L−1)/2) |
| `palprimes` | number of those palindromes that are prime |

The counts were computed with `numerics/counts/palcount.c`, which uses trial division and a deterministic
Miller–Rabin test for n < 2^64. They were checked against brute force for 93 small (b, L) pairs and against
OEIS A016115 for base 10 up to L = 19 (239 093 865 palprimes with 19 digits).
