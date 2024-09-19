from itertools import product
from concurrent.futures import ProcessPoolExecutor, wait, ALL_COMPLETED
from multiprocessing import cpu_count
import random
import time


def feistel(plaintext, keys, rounds):

    # Feistel cipher using bitwise and as the feistel function

    # Base case - no rounds left
    if rounds == 0:
        return plaintext

    # If keys is given as a single rt bytes, convert to a tuple of r lots of t length bytes.
    if type(keys) == bytes:
        if len(keys) % rounds != 0:
            raise ValueError('keys is not divisible by remaining rounds')
        step = len(keys) // rounds
        keys = [keys[i:i+step] for i in range(0, len(keys), step)]

    # Extract the key for this round
    key = keys[0]

    # Split into left and right t length bytes
    if type(plaintext) == bytes:
        if len(plaintext) % 2 != 0:
            raise ValueError('plaintext is not divisible by 2')
        mid = len(plaintext) // 2
        l, r = plaintext[:mid], plaintext[mid:]
    elif type(plaintext) == tuple or type(plaintext) == list and len(plaintext) == 2:
        l, r = plaintext[0], plaintext[1]
    else:
        raise TypeError('Bad type for plaintext')

    l_i, r_i = [], []        

    # Compute feistel for this round
    for bl, br, bk in zip(l, r, key):
        l_i.append(br)
        r_i.append(bl ^ (br & bk))
    
    # Convert back into bytes
    ciphertext = bytes(l_i + r_i)

    # Recursive call
    return feistel(ciphertext, keys[1:], rounds-1)


def fast_feistel(plaintext, keys, rounds):

    # Faster vertsion of feistel function
    # Assumes plaintext is a two tuple of ints, keys is a list of r ints
    # Returns ciphertext in the same form.

    if rounds == 0:
        return plaintext

    key = keys[0]

    l_i = plaintext[1]
    r_i = plaintext[0] ^ (l_i & key)

    return fast_feistel((l_i, r_i), keys[1:], rounds-1)


def defeistel(ciphertext, keys, rounds):

    # Reverse feistel cipher again using bitwise and as the feistal function

    # Base case - no rounds left
    if rounds == 0:
        return ciphertext

    # If keys is given as a single rt bytes, convert to a tuple of r lots of t length bytes.
    if type(keys) == bytes:
        if len(keys) % rounds != 0:
            raise ValueError('keys is not divisible by remaining rounds')
        step = len(keys) // rounds
        keys = [keys[i:i+step] for i in range(0, len(keys), step)]
    
    # Extract the key for this round
    key = keys[-1]

    # Split into left and right t length bytes
    if type(ciphertext) == bytes:
        if len(ciphertext) % 2 != 0:
            raise ValueError('ciphertext is not divisible by 2')
        mid = len(ciphertext) // 2
        l, r = ciphertext[:mid], ciphertext[mid:]
    elif type(ciphertext) == list or type(ciphertext) == tuple and len(ciphertext) == 2:
        l, r = ciphertext[0], ciphertext[1]
    else:
        raise TypeError('Bad type for ciphertext')
    
    l_i, r_i = [], []

    # Compute defeistel for this round
    for bl, br, bk in zip(l, r, key):
        r_i.append(bl)
        l_i.append(br ^ (bl & bk))

    # Convert back into bytes
    plaintext = bytes(l_i + r_i)

    # Recursive call
    return defeistel(plaintext, keys[:-1], rounds-1)


def extract_bits(plaintext, ciphertext, output_size=1):

    # Helper generator for extracting bit pairs from the left and right of plaintext and ciphertext
    # Returns a tuple of ints
    # output_size describes how many bits are being extracted. Must be 1, 2, 4, or 8

    if type(plaintext) == tuple or type(plaintext) == list and len(ciphertext) == 2:
        ptl, ptr = plaintext[0], plaintext[1]
    elif type(plaintext) == bytes:
        mid = len(plaintext) // 2
        ptl, ptr = plaintext[:mid], plaintext[mid:]
    else:
        raise TypeError('Bad type for plaintext')
    
    if type(ciphertext) == tuple or type(ciphertext) == list and len(ciphertext) == 2:
        ctl, ctr = ciphertext[0], ciphertext[1]
    elif type(ciphertext) == bytes:
        mid = len(ciphertext) // 2
        ctl, ctr = ciphertext[:mid], ciphertext[mid:]
    else:
        raise TypeError('Bad type for ciphertext')

    if not (len(ptl) == len(ptr) == len(ctl) == len(ctr)):
        raise ValueError(f'Plaintext and Ciphertext different sizes {len(ptl), len(ptr), len(ctl), len(ctr)}')

    s = 2**output_size - 1
    for pl, pr, cl, cr in list(zip(ptl, ptr, ctl, ctr))[::-1]:
        for i in range(0, 8, output_size):
            yield (pl >> i) & s, (pr >> i) & s, (cl >> i) & s, (cr >> i) & s


def compute_key_lookup(r, size):

    # Outputs a dictionary with a mapping of (ptl ptr ctl ctr) -> (key)
    # r specifies the number of rounds and length of key.
    # size specifies the number of bits

    key_lookup = {}
    mx = 2**size
    rnge = tuple(range(mx))
    for pl, pr, cl, cr in product(rnge, repeat=4):
        for k in product(rnge, repeat=3):
            k = [mx-1]*(r-3) + [k[0], k[1], k[2]]
            if fast_feistel((pl, pr), k, r) == (cl, cr):
                key_lookup[(pl, pr, cl, cr)] = k
                break
    
    return key_lookup


def crackrround(plaintext, ciphertext, rounds, key_lookup = None, lookup_size = 1):

    # Cracks an r round feistel cipher

    # Compute all plaintext, ciphertext pairs
    if not key_lookup:
        key_lookup = compute_key_lookup(rounds, lookup_size)

    # Initialise empty ley
    key = [list() for _ in range(rounds)]

    # Iterate through all plaintext and ciphertext pairs to reconstruct the key
    for i, ptct in enumerate(extract_bits(plaintext, ciphertext, lookup_size)):
        for j, k in enumerate(key_lookup[ptct]):
            if i % (8 // lookup_size) == 0:
                key[j].insert(0, 0)
            key[j][0] |= k << ((i * lookup_size) % 8)

    out = []
    for k in key:
        out += k

    # Convert output to bytes
    return bytes(out)


def crackrround_thread(plaintext, ciphertext, rounds, key_lookup, lookup_size):
    
    # Iterates through all plaintext and ciphertext pairs to reconstruct the key
    
    # Initialise possible key list
    key = [list() for _ in range(rounds)]

    for i, ptct in enumerate(extract_bits(plaintext, ciphertext, lookup_size)):
        for j, k in enumerate(key_lookup[ptct]):
            if i % (8 // lookup_size) == 0:
                key[j].insert(0, 0)
            key[j][0] |= k << ((i * lookup_size) % 8)
    
    out = []
    for k in key:
        out += k

    # Convert output to bytes
    return bytes(out)


def crackrround_mt(plaintext, ciphertext, rounds, key_lookup = None, lookup_size = 1):

    # Multithreaded implementation of crackrround - doesn't work

    # Precompute all plaintext, ciphertext pairs
    if not key_lookup:
        key_lookup = compute_key_lookup(rounds, lookup_size)
        
    t = len(plaintext) // 2
    t_slice = 16 if t % 16 == 0 else 4

    # Split into blocks
    pt_blocks = [bytes(plaintext[i:i+t_slice] + plaintext[t+i:t+i+t_slice]) for i in range(0, t, t_slice)]
    ct_blocks = [bytes(ciphertext[i:i+t_slice] + ciphertext[t+i:t+i+t_slice]) for i in range(0, t, t_slice)]

    # Create a process for each block
    with ProcessPoolExecutor(max_workers=cpu_count()) as executor:
        processes = []

        for pt, ct in zip(pt_blocks, ct_blocks):
            p = executor.submit(crackrround_thread, pt, ct, rounds, key_lookup, lookup_size)
            processes.append(p)
        
        keys, _ = wait(processes, return_when=ALL_COMPLETED)
        keys = [k.result() for k in keys]
        executor.shutdown()
    
    # Recombine keys - This is the worst code I think I've ever written
    out = [list() for _ in range(rounds)]
    for k_block in keys:
        for i in range(rounds):
            out[i] += k_block[t_slice*i:t_slice*(i+1)]
    
    new_out = []
    for k in out:
        new_out += k
    
    # Convert output to bytes
    return bytes(new_out)


def crack3round(plaintext, ciphertext, *kwargs):
    kl = {(0, 0, 0, 0): (0, 0, 0), (0, 1, 0, 1): (1, 1, 0), (0, 1, 1, 0): (0, 0, 0), (0, 1, 1, 1): (0, 0, 1), (0, 2, 0, 2): (2, 2, 0), (0, 2, 2, 0): (0, 0, 0), (0, 2, 2, 2): (0, 0, 2), (0, 3, 0, 3): (3, 3, 0), (0, 3, 1, 2): (2, 2, 0), (0, 3, 1, 3): (2, 2, 1), (0, 3, 2, 1): (1, 1, 0), (0, 3, 2, 3): (1, 1, 2), (0, 3, 3, 0): (0, 0, 0), (0, 3, 3, 1): (0, 0, 1), (0, 3, 3, 2): (0, 0, 2), (0, 3, 3, 3): (0, 0, 3), (1, 0, 0, 1): (0, 0, 0), (1, 0, 1, 0): (0, 1, 1), (1, 0, 1, 1): (0, 1, 0), (1, 1, 0, 1): (0, 1, 0), (1, 1, 1, 0): (0, 0, 1), (1, 1, 1, 1): (0, 0, 0), (1, 2, 0, 3): (2, 2, 0), (1, 2, 1, 2): (2, 3, 1), (1, 2, 1, 3): (2, 3, 0), (1, 2, 2, 1): (0, 0, 0), (1, 2, 2, 3): (0, 0, 2), (1, 2, 3, 0): (0, 1, 1), (1, 2, 3, 1): (0, 1, 0), (1, 2, 3, 2): (0, 1, 3), (1, 2, 3, 3): (0, 1, 2), (1, 3, 0, 3): (2, 3, 0), (1, 3, 1, 2): (2, 2, 1), (1, 3, 1, 3): (2, 2, 0), (1, 3, 2, 1): (0, 1, 0), (1, 3, 2, 3): (0, 1, 2), (1, 3, 3, 0): (0, 0, 1), (1, 3, 3, 1): (0, 0, 0), (1, 3, 3, 2): (0, 0, 3), (1, 3, 3, 3): (0, 0, 2), (2, 0, 0, 2): (0, 0, 0), (2, 0, 2, 0): (0, 2, 2), (2, 0, 2, 2): (0, 2, 0), (2, 1, 0, 3): (1, 1, 0), (2, 1, 1, 2): (0, 0, 0), (2, 1, 1, 3): (0, 0, 1), (2, 1, 2, 1): (1, 3, 2), (2, 1, 2, 3): (1, 3, 0), (2, 1, 3, 0): (0, 2, 2), (2, 1, 3, 1): (0, 2, 3), (2, 1, 3, 2): (0, 2, 0), (2, 1, 3, 3): (0, 2, 1), (2, 2, 0, 2): (0, 2, 0), (2, 2, 2, 0): (0, 0, 2), (2, 2, 2, 2): (0, 0, 0), (2, 3, 0, 3): (1, 3, 0), (2, 3, 1, 2): (0, 2, 0), (2, 3, 1, 3): (0, 2, 1), (2, 3, 2, 1): (1, 1, 2), (2, 3, 2, 3): (1, 1, 0), (2, 3, 3, 0): (0, 0, 2), (2, 3, 3, 1): (0, 0, 3), (2, 3, 3, 2): (0, 0, 0), (2, 3, 3, 3): (0, 0, 1), (3, 0, 0, 3): (0, 0, 0), (3, 0, 1, 2): (0, 1, 1), (3, 0, 1, 3): (0, 1, 0), (3, 0, 2, 1): (0, 2, 2), (3, 0, 2, 3): (0, 2, 0), (3, 0, 3, 0): (0, 3, 3), (3, 0, 3, 1): (0, 3, 2), (3, 0, 3, 2): (0, 3, 1), (3, 0, 3, 3): (0, 3, 0), (3, 1, 0, 3): (0, 1, 0), (3, 1, 1, 2): (0, 0, 1), (3, 1, 1, 3): (0, 0, 0), (3, 1, 2, 1): (0, 3, 2), (3, 1, 2, 3): (0, 3, 0), (3, 1, 3, 0): (0, 2, 3), (3, 1, 3, 1): (0, 2, 2), (3, 1, 3, 2): (0, 2, 1), (3, 1, 3, 3): (0, 2, 0), (3, 2, 0, 3): (0, 2, 0), (3, 2, 1, 2): (0, 3, 1), (3, 2, 1, 3): (0, 3, 0), (3, 2, 2, 1): (0, 0, 2), (3, 2, 2, 3): (0, 0, 0), (3, 2, 3, 0): (0, 1, 3), (3, 2, 3, 1): (0, 1, 2), (3, 2, 3, 2): (0, 1, 1), (3, 2, 3, 3): (0, 1, 0), (3, 3, 0, 3): (0, 3, 0), (3, 3, 1, 2): (0, 2, 1), (3, 3, 1, 3): (0, 2, 0), (3, 3, 2, 1): (0, 1, 2), (3, 3, 2, 3): (0, 1, 0), (3, 3, 3, 0): (0, 0, 3), (3, 3, 3, 1): (0, 0, 2), (3, 3, 3, 2): (0, 0, 1), (3, 3, 3, 3): (0, 0, 0)}
    return crackrround(plaintext, ciphertext, 3, key_lookup = kl, lookup_size = 2)


def crack4round(plaintext, ciphertext, *kwargs):
    kl = {(0, 0, 0, 0): (0, 0, 0, 0), (0, 1, 0, 1): (0, 0, 0, 0), (0, 1, 1, 0): (0, 0, 1, 1), (0, 1, 1, 1): (0, 0, 1, 0), (0, 2, 0, 2): (0, 0, 0, 0), (0, 2, 2, 0): (0, 0, 2, 2), (0, 2, 2, 2): (0, 0, 2, 0), (0, 3, 0, 3): (0, 0, 0, 0), (0, 3, 1, 2): (0, 0, 1, 1), (0, 3, 1, 3): (0, 0, 1, 0), (0, 3, 2, 1): (0, 0, 2, 2), (0, 3, 2, 3): (0, 0, 2, 0), (0, 3, 3, 0): (0, 0, 3, 3), (0, 3, 3, 1): (0, 0, 3, 2), (0, 3, 3, 2): (0, 0, 3, 1), (0, 3, 3, 3): (0, 0, 3, 0), (1, 0, 0, 1): (0, 1, 1, 0), (1, 0, 1, 0): (0, 0, 0, 0), (1, 0, 1, 1): (0, 0, 0, 1), (1, 1, 0, 1): (0, 0, 1, 0), (1, 1, 1, 0): (0, 0, 0, 1), (1, 1, 1, 1): (0, 0, 0, 0), (1, 2, 0, 3): (0, 1, 1, 0), (1, 2, 1, 2): (0, 0, 0, 0), (1, 2, 1, 3): (0, 0, 0, 1), (1, 2, 2, 1): (0, 1, 3, 2), (1, 2, 2, 3): (0, 1, 3, 0), (1, 2, 3, 0): (0, 0, 2, 2), (1, 2, 3, 1): (0, 0, 2, 3), (1, 2, 3, 2): (0, 0, 2, 0), (1, 2, 3, 3): (0, 0, 2, 1), (1, 3, 0, 3): (0, 0, 1, 0), (1, 3, 1, 2): (0, 0, 0, 1), (1, 3, 1, 3): (0, 0, 0, 0), (1, 3, 2, 1): (0, 0, 3, 2), (1, 3, 2, 3): (0, 0, 3, 0), (1, 3, 3, 0): (0, 0, 2, 3), (1, 3, 3, 1): (0, 0, 2, 2), (1, 3, 3, 2): (0, 0, 2, 1), (1, 3, 3, 3): (0, 0, 2, 0), (2, 0, 0, 2): (0, 2, 2, 0), (2, 0, 2, 0): (0, 0, 0, 0), (2, 0, 2, 2): (0, 0, 0, 2), (2, 1, 0, 3): (0, 2, 2, 0), (2, 1, 1, 2): (0, 2, 3, 1), (2, 1, 1, 3): (0, 2, 3, 0), (2, 1, 2, 1): (0, 0, 0, 0), (2, 1, 2, 3): (0, 0, 0, 2), (2, 1, 3, 0): (0, 0, 1, 1), (2, 1, 3, 1): (0, 0, 1, 0), (2, 1, 3, 2): (0, 0, 1, 3), (2, 1, 3, 3): (0, 0, 1, 2), (2, 2, 0, 2): (0, 0, 2, 0), (2, 2, 2, 0): (0, 0, 0, 2), (2, 2, 2, 2): (0, 0, 0, 0), (2, 3, 0, 3): (0, 0, 2, 0), (2, 3, 1, 2): (0, 0, 3, 1), (2, 3, 1, 3): (0, 0, 3, 0), (2, 3, 2, 1): (0, 0, 0, 2), (2, 3, 2, 3): (0, 0, 0, 0), (2, 3, 3, 0): (0, 0, 1, 3), (2, 3, 3, 1): (0, 0, 1, 2), (2, 3, 3, 2): (0, 0, 1, 1), (2, 3, 3, 3): (0, 0, 1, 0), (3, 0, 0, 3): (0, 3, 3, 0), (3, 0, 1, 2): (0, 2, 2, 0), (3, 0, 1, 3): (0, 2, 2, 1), (3, 0, 2, 1): (0, 1, 1, 0), (3, 0, 2, 3): (0, 1, 1, 2), (3, 0, 3, 0): (0, 0, 0, 0), (3, 0, 3, 1): (0, 0, 0, 1), (3, 0, 3, 2): (0, 0, 0, 2), (3, 0, 3, 3): (0, 0, 0, 3), (3, 1, 0, 3): (0, 2, 3, 0), (3, 1, 1, 2): (0, 2, 2, 1), (3, 1, 1, 3): (0, 2, 2, 0), (3, 1, 2, 1): (0, 0, 1, 0), (3, 1, 2, 3): (0, 0, 1, 2), (3, 1, 3, 0): (0, 0, 0, 1), (3, 1, 3, 1): (0, 0, 0, 0), (3, 1, 3, 2): (0, 0, 0, 3), (3, 1, 3, 3): (0, 0, 0, 2), (3, 2, 0, 3): (0, 1, 3, 0), (3, 2, 1, 2): (0, 0, 2, 0), (3, 2, 1, 3): (0, 0, 2, 1), (3, 2, 2, 1): (0, 1, 1, 2), (3, 2, 2, 3): (0, 1, 1, 0), (3, 2, 3, 0): (0, 0, 0, 2), (3, 2, 3, 1): (0, 0, 0, 3), (3, 2, 3, 2): (0, 0, 0, 0), (3, 2, 3, 3): (0, 0, 0, 1), (3, 3, 0, 3): (0, 0, 3, 0), (3, 3, 1, 2): (0, 0, 2, 1), (3, 3, 1, 3): (0, 0, 2, 0), (3, 3, 2, 1): (0, 0, 1, 2), (3, 3, 2, 3): (0, 0, 1, 0), (3, 3, 3, 0): (0, 0, 0, 3), (3, 3, 3, 1): (0, 0, 0, 2), (3, 3, 3, 2): (0, 0, 0, 1), (3, 3, 3, 3): (0, 0, 0, 0)}
    return crackrround(plaintext, ciphertext, 4, key_lookup = kl, lookup_size = 2)


def crack10round(plaintext, ciphertext):
    return crackrround(plaintext, ciphertext, 10)


def cipherhash(hashinput):

    z = bytes([255] * 8)
    l = len(hashinput)
    n = 16
    
    # Pad with 0s
    hashinput = bytes(list(hashinput) + (n-l % n)*[0])
    
    # Split into 128-bit blocks
    blocks = [hashinput[i:i+n] for i in range(0, l, n)]

    # Add an additional block encoding the length of the original message
    L = bytes([((l*8) >> i) & 255 for i in range(0, 128, 8)][::-1])
    blocks.append(L)

    # Iteratively compute z_i
    for x in blocks:
        # Compute h(z, x)
        h = feistel(z, x, 4)
        # Bitwise XOR with z
        z = bytes([h_i^z_i for h_i, z_i in zip(h, z)])

    return bytes(z)


def random_bytes(t):

    # Generates a random bytes instance of t bits

    out = []
    for i in range(t):
        if i % 8 == 0:
            out.insert(0, 0)
        out[0] |= random.randint(0, 1) << (i % 8)
    return bytes(out)


def test_feistel_crack(cracker, t, r, iterations=1000):

    # Tests a cracker function on a random t-bit input
    # Returns the % of successful cracks

    count = 0
    for _ in range(iterations):
        M = random_bytes(2*t)
        key = random_bytes(r*t)
        C = feistel(M, key, r)
        key_prime = cracker(M, C, r)
        if feistel(M, key_prime, r) == C:
            # print(f'{M} + {key_prime} --> {C}')
            count += 1
        else:
            print(f'Failure')
    return (count / iterations) * 100


# if __name__ == '__main__':

#     times = []
#     for r in range(3, 11):  
#         current_time = time.perf_counter()
#         test_feistel_crack(crackrround, 10000, r, 100)
#         times.append((time.perf_counter() - current_time) / 100)