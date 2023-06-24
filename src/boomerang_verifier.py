import numpy as np
from os import urandom

def WORD_SIZE():
    return(16);

def ALPHA():
    return(7);

def BETA():
    return(2);

MASK_VAL = 2 ** WORD_SIZE() - 1;

def rol(x,k):
    return(((x << k) & MASK_VAL) | (x >> (WORD_SIZE() - k)));

def ror(x,k):
    return((x >> k) | ((x << (WORD_SIZE() - k)) & MASK_VAL));

def enc_one_round(p, k):
    c0, c1 = p[0], p[1];
    c0 = ror(c0, ALPHA());
    c0 = (c0 + c1) & MASK_VAL;
    c0 = c0 ^ k;
    c1 = rol(c1, BETA());
    c1 = c1 ^ c0;
    return(c0,c1);

def dec_one_round(c,k):
    c0, c1 = c[0], c[1];
    c1 = c1 ^ c0;
    c1 = ror(c1, BETA());
    c0 = c0 ^ k;
    c0 = (c0 - c1) & MASK_VAL;
    c0 = rol(c0, ALPHA());
    return(c0, c1);

def expand_key(k, t):
    ks = [0 for i in range(t)];
    ks[0] = k[len(k)-1];
    l = list(reversed(k[:len(k)-1]));
    for i in range(t-1):
        l[i%3], ks[i+1] = enc_one_round((l[i%3], ks[i]), i);
    return(ks);

def encrypt(p, ks):
    x, y = p[0], p[1];
    for k in ks:
        x,y = enc_one_round((x,y), k);
    return(x, y);

def decrypt(c, ks):
    x, y = c[0], c[1];
    for k in reversed(ks):
        x, y = dec_one_round((x,y), k);
    return(x,y);

def verify_related_key(key_diff, delta_subkey_diff, nabla, delta, nr, n=2**10):
    keys = np.frombuffer(urandom(8*n),dtype=np.uint16).reshape(4,-1);
    plain0l = np.frombuffer(urandom(2*n),dtype=np.uint16);
    plain0r = np.frombuffer(urandom(2*n),dtype=np.uint16);
    plain1l = plain0l ^ nabla[0]; plain1r = plain0r ^ nabla[1]; keys_diff = keys ^ np.array(key_diff)[:, np.newaxis]
    ks = expand_key(keys, nr);
    ks_diff = expand_key(keys_diff, nr);

    # Compute C0 = E_K(P0), C1 = E_K(P0^nabla) (for nr rounds)
    ctdata0l, ctdata0r = encrypt((plain0l, plain0r), ks);
    ctdata1l, ctdata1r = encrypt((plain1l, plain1r), ks_diff);

    # Compute C2 = C0^delta, C3 = C1^delta
    ctdata2l = ctdata0l^delta[0]; ctdata2r = ctdata0r^delta[1]
    ctdata3l = ctdata1l^delta[0]; ctdata3r = ctdata1r^delta[1]
    ctsubkey2 = ks_diff[len(ks_diff)-1] ^ delta_subkey_diff
    ctsubkey3 = ks[len(ks)-1] ^ delta_subkey_diff

    # Compute P2 = D_K(C2), P3 = D_K(C3)
    plain2l, plain2r = decrypt((ctdata2l, ctdata2r), ks)
    plain3l, plain3r = decrypt((ctdata3l, ctdata3r), ks_diff)

    Nabla = (np.uint32(nabla[0])<<16)^nabla[1]
    # Compute P2^P3
    Nabla_prime = (np.uint32(plain2l^plain3l)<<16)^plain2r^plain3r

    # Count how many times the boomerang returned
    total = np.sum(Nabla_prime == Nabla)
    return total/n

#baseline training data generator
def verify(nabla, delta, nr, n=2**26):
    keys = np.frombuffer(urandom(8*n),dtype=np.uint16).reshape(4,-1);
    keys_diff = np.frombuffer(urandom(8*n),dtype=np.uint16).reshape(4,-1);
    plain0l = np.frombuffer(urandom(2*n),dtype=np.uint16);
    plain0r = np.frombuffer(urandom(2*n),dtype=np.uint16);
    sub_key = np.frombuffer(urandom(n),dtype=np.uint16);
    plain1l = plain0l ^ nabla[0]; plain1r = plain0r ^ nabla[1]; keys_diff = keys ^ key_diff
    ks = expand_key(keys, nr);
    ks_diff = expand_key(keys_diff, nr);

    # Compute C0 = E_K(P0), C1 = E_K(P0^nabla) (for nr rounds)
    ctdata0l, ctdata0r = encrypt((plain0l, plain0r), ks);
    ctdata1l, ctdata1r = encrypt((plain1l, plain1r), ks_diff);

    # Compute C2 = C0^delta, C3 = C1^delta
    ctdata2l = ctdata0l^delta[0]; ctdata2r = ctdata0r^delta[1]
    ctdata3l = ctdata1l^delta[0]; ctdata3r = ctdata1r^delta[1]

    # Compute P2 = D_K(C2), P3 = D_K(C3)
    plain2l, plain2r = decrypt((ctdata2l, ctdata2r), ks)
    plain3l, plain3r = decrypt((ctdata3l, ctdata3r), ks)

    Nabla = (np.uint32(nabla[0])<<16)^nabla[1]
    # Compute P2^P3
    Nabla_prime = (np.uint32(plain2l^plain3l)<<16)^plain2r^plain3r

    # Count how many times the boomerang returned
    total = np.sum(Nabla_prime == Nabla)
    return total/n

#baseline training data generator
def verify_differential_single_key_forward(delta, nabla, nr, n=2**26):
    keys = np.frombuffer(urandom(8*n),dtype=np.uint16).reshape(4,-1);
    plain0l = np.frombuffer(urandom(2*n),dtype=np.uint16);
    plain0r = np.frombuffer(urandom(2*n),dtype=np.uint16);
    plain1l = plain0l ^ delta[0]; plain1r = plain0r ^ delta[1];
    ks = expand_key(keys, nr);

    ctdata0l, ctdata0r = encrypt((plain0l, plain0r), ks);
    ctdata1l, ctdata1r = encrypt((plain1l, plain1r), ks);



    Nabla = (np.uint32(nabla[0])<<16)^nabla[1]
    Nabla_prime = (np.uint32(ctdata0l^ctdata1l)<<16)^ctdata0r^ctdata1r

    # Count how many times the boomerang returned
    total = np.sum(Nabla_prime == Nabla)
    return total/n


#baseline training data generator
def verify_differential_related_key_forward(delta, nabla, delta_key, nr, n=2):
    keys = np.frombuffer(urandom(8*n),dtype=np.uint16).reshape(4,-1);
    plain0l = np.frombuffer(urandom(2*n),dtype=np.uint16);
    plain0r = np.frombuffer(urandom(2*n),dtype=np.uint16);
    plain1l = plain0l ^ delta[0]; plain1r = plain0r ^ delta[1];
    keys_diff = keys ^ np.array(delta_key)[:, np.newaxis]
    ks = expand_key(keys, nr);
    ks_diff = expand_key(keys_diff, nr);

    ctdata0l, ctdata0r = encrypt((plain0l, plain0r), ks);
    ctdata1l, ctdata1r = encrypt((plain1l, plain1r), ks_diff);

    Nabla = (np.uint32(nabla[0])<<16)^nabla[1]
    Nabla_prime = (np.uint32(ctdata0l^ctdata1l)<<16)^ctdata0r^ctdata1r

    # Count how many times the boomerang returned
    total = np.sum(Nabla_prime == Nabla)
    print("Total", total)
    return total/n

def verify_differential_related_key_backward(delta, nabla, delta_key, nr, n=2):
    keys = np.frombuffer(urandom(8*n),dtype=np.uint16).reshape(4,-1);
    plain0l = np.frombuffer(urandom(2*n),dtype=np.uint16);
    plain0r = np.frombuffer(urandom(2*n),dtype=np.uint16);
    plain1l = plain0l ^ delta[0]; plain1r = plain0r ^ delta[1];
    keys_diff = keys ^ np.array(delta_key)[:, np.newaxis]
    ks = expand_key(keys, nr);
    ks_diff = expand_key(keys_diff, nr);

    ctdata0l, ctdata0r = decrypt((plain0l, plain0r), ks);
    ctdata1l, ctdata1r = decrypt((plain1l, plain1r), ks_diff);

    Nabla = (np.uint32(nabla[0])<<16)^nabla[1]
    Nabla_prime = (np.uint32(ctdata0l^ctdata1l)<<16)^ctdata0r^ctdata1r

    # Count how many times the boomerang returned
    total = np.sum(Nabla_prime == Nabla)
    print("Total", total)
    return total/n

#baseline training data generator
def verify_differential_single_key_backward(delta, nabla, nr, n=2**26):
    keys = np.frombuffer(urandom(8*n),dtype=np.uint16).reshape(4,-1);
    plain0l = np.frombuffer(urandom(2*n),dtype=np.uint16);
    plain0r = np.frombuffer(urandom(2*n),dtype=np.uint16);
    plain1l = plain0l ^ delta[0]; plain1r = plain0r ^ delta[1];
    ks = expand_key(keys, nr);

    ctdata0l, ctdata0r = decrypt((plain0l, plain0r), ks);
    ctdata1l, ctdata1r = decrypt((plain1l, plain1r), ks);

    Nabla = (np.uint32(nabla[0])<<16)^nabla[1]
    Nabla_prime = (np.uint32(ctdata0l^ctdata1l)<<16)^ctdata0r^ctdata1r


    # Count how many times the boomerang returned
    total = np.sum(Nabla_prime == Nabla)
    return total/n

#nr = 6
#delta = (0x0211, 0x0A04)
#nabla = (0x8532, 0x9508)
#probability = verify_differential_single_key_forward(delta, nabla, nr)
#probability = verify_differential_single_key_backward(nabla, delta, nr)


# 3dc6bec8-fc5e-4f25-8dfc-13fc47a2f4a2
nr = 7
delta = (0x0205, 0x0200)
nabla = (0x0102, 0x0100)
delta_key = (0x0000, 0x2800, 0x0200, 0x0004)
#probability = verify_differential_related_key_forward(delta, nabla, delta_key, nr, n=2**23)
#probability = verify_differential_related_key_backward(nabla, delta, delta_key, nr, n=2**23)

# Table 9 journals/dcc/SadeghiRB21
nr = 7
delta = (0x0204, 0x0005)
nabla = (0x8000, 0x8000)
delta_key = (0x2800, 0x0200, 0x0080, 0x0001)
probability = verify_differential_related_key_forward(delta, nabla, delta_key, nr, n=2**23)
#probability = verify_differential_related_key_backward(nabla, delta, delta_key, nr, n=2**23)


#subkey_delta = (0x1)
#probability = verify(nabla, delta, nr)
#probability = verify_related_key(key_diff_nabla, subkey_delta, nabla, delta, nr)

print(f'The probability for the boomerang {(hex(delta[0]), hex(delta[1]))} <-{nr}-> {(hex(nabla[0]), hex(nabla[1]))} is 2^{np.log2(probability)}')