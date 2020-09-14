from random import random
from random import randint
from sage.all import *
from fpylll import BKZ
from fpylll import CVP
from fpylll import IntegerMatrix
import sys
import numpy as np


def get_primes(start, n):
    """
	Get a list of primes of length n which are all bigger than start in asending order.

	Input: start, n
	start: integer number
	n: number of primes output
	Output: plist
	plist: a list of prime numbers of length n, each element is larger than start
	"""

    plist = list()
    plist.append(next_prime(start))
    for i in range(n - 1):
        plist.append(next_prime(plist[-1]))
    return plist


def gen_params(n, t, p0, s):
    """
	Generate parameters for the secret sharing scheme.

	Input: n, t, p0, s
	n: number of total participants.
	t: threshold. t shares can recover the secret.
	p0: field size of the secret range.
	s: the secret to be shared.
	Output: plist
	plist: a list of primes of length n, satisfying the properties as follows:
		   1. p_1 < p_2 < ... < p_n
		   2. n * p_0^3 / (p0 -1) < plist[0]
		   3. p0^2*\prod_{i = n-t+2}^{n} p_i < p_1 * ... * p_t
	"""
    #print "----------------- begin gen_params() -------------------"
    #print "n = ", n
    #print "t = ", t
    z = ceil(n * p0 ** 3 / (p0 - 1))
    #print "z (n * p0 ** 3 / (p0 - 1)) = ", z
    plist = get_primes(z, n)
    #print "Prime list is ", plist
    H = reduce(
        lambda x, y: x * y, plist[:t]
    )  # Head of the primes product p_1 * ... * p_t
    T = reduce(
        lambda x, y: x * y, plist[n - t + 1 :]
    )  # Tail of the primes product p_{n-t+2} * ... * p_n
    #print "H = ", H
    #print "T = ", T
    if p0 * p0 * T >= H:
        print "Parameter not correctly set, exit!"
        sys.exit()
    #print "------------------ end gen_params() --------------------"
    return plist


def crt_prepare(mlist):
    """
	Prepare the solution for the modular equations x = alist[i] mod mlist[i] via Chinese Remainder Theorem.

	Input: mlist
	mlist: a list, the modulis of the equations
	Output: Mlist, ylist
	Mlist: Mlist[i] = prod(mlist) / mlist[i]
	ylist: ylist[i] = (Mlist[i])^{-1} mod mlist[i]
	"""

    M = reduce(lambda x, y: x * y, mlist)
    Mlist = [int(M / m) for m in mlist]
    ylist = list()
    ylist = [inverse_mod(a, int(b)) for (a, b) in zip(Mlist, mlist)]
    return (Mlist, ylist)


def share_gen(n, t, p0, s):
    """
	Share generating function.

	Input: n, t, p0, s
	n: number of total participants.
	t: threshold. t shares can recover the secret.
	p0: field size of the secret range.
	s: the secret to be shared.
	Output: sharelist
	sharelist: the list of shares of all the n participants.
			   Each element in sharelist is a tuple (p_i, s_i),
			   where p_i is the public moduli of player i and
			   s_i is her share.
	"""

    #print "------------------- begin share_gen() ---------------------"
    n = int(n)
    t = int(t)
    p0 = int(p0)
    s = int(s)
    #print "n = ", n
    #print "t = ", t
    #print "s = ", s
    Fp = GF(p0)
    plist = gen_params(n, t, p0, s)
    H = reduce(lambda x, y: x * y, plist[:t])
    amax = int(H / (p0 * p0)) - 1
    a = random() * amax
    a = int(a)
    x = s + a * p0
    print "s + a*p0 = ", x
    sharelist = list()
    for p in plist:
        si = x % p
        sharelist.append((p, si))
    print 'sharelist is'
    print sharelist
    #print "------------------- end share_gen() ---------------------"
    return sharelist


def gen_rc(sharelist, ulist, p0):
    """
	Generate random components from the shares of players in ulist.

	Input: sharelist, ulist
	sharelist: the list of shares of all players, each share is of type (pi, si).
	ulist: the identity list of the participating players in the reconstruction phase.
	p0: size of the secret field.
	Output: rclist
	rclist: the list of random components generated.
	N: the product of all modulis from shares of ulist.
	"""
    print "-------------------- begin gen_rc() -------------------------"
    share_in_use = [sharelist[i - 1] for i in ulist]
    si_list = list()
    pi_list = list()

    for pi, si in share_in_use:
        si_list.append(si)
        pi_list.append(pi)
    N = reduce(lambda x, y: x * y, pi_list)
    Mlist, ylist = crt_prepare(pi_list)
    rc_list = list()
    r_list = list()
    additive_random_list = list()
    for si, Mi, yi in zip(si_list, Mlist, ylist):
        r = randint(0, p0 - 1)
        r_list.append(r)
        rc = (si * Mi * yi + r * Mi * p0) % N
        rc_list.append(rc)
        additive_random = r * Mi * p0
        additive_random_list.append(additive_random)
    print "random list ", r_list
    #print "additive random list ", additive_random_list
    #print "sum of addtive randomness is ", sum(additive_random_list)
    #print "Mlist ", Mlist
    #print "ylist ", ylist
    print "rclist ", rc_list
    #print "-------------------- end gen_rc() -------------------------"
    return (rc_list, r_list, pi_list, N)


def reconst_from_share(sharelist, ulist, p0):
    """
	Reconstruct the secret from sharelist.

	Input: sharelist, ulist, p0
	sharelist: the list of shares of all the n parties.
	ulist: the list of the identity of m parties in the reconstruction phase.
	p0: the size of the filed from which the secret is taken.
	Output: secret_from_share, rc_list, pi_list
	secret_from_share: the secret recovered from the shares from the parties in ulist.
	rc_list: the components computed from the shares.
	pi_list: list of the modulis used for the parties in ulist.
	"""

    #print "-------------------- begin reconst_from_share() -------------------------"
    share_in_use = [sharelist[i - 1] for i in ulist]
    si_list = list()
    pi_list = list()
    for pi, si in share_in_use:
        pi_list.append(pi)
        si_list.append(si)
    N = reduce(lambda x, y: x * y, pi_list)
    Mlist, ylist = crt_prepare(pi_list)
    rc_list = list()
    for si, Mi, yi in zip(si_list, Mlist, ylist):
        rc = si * Mi * yi % N
        rc_list.append(rc)
    secret_from_share = sum(rc_list) % N
    secret_from_share = secret_from_share % p0
    #print "---------------------- end reconst_from_share() -------------------------"
    return secret_from_share, rc_list, pi_list


def reconst_from_share_missing1(rc_list, pi_list, p0):
    """
	Reconstruct the secret from components with the last component missing.

	Input: rc_list, pi_list, p0
	rc_list: component computed from the shares, list of size m.
	pi_list: modulis used for the shares, list of size m.
	p0: size of the secret field.
	Output: secret_from_share_missing1
	secret_from_share_missing1: the secret recovered from the components with the last one missing.
	"""

    N = reduce(lambda x, y: x * y, pi_list)
    N_prime = N / pi_list[-1]
    pi_list_prime = pi_list[:-1]
    x_list = list()
    for rc, pi in zip(rc_list[:-1], pi_list_prime):
        xi = rc % pi
        x_list.append(xi)
    #print "x_list ", x_list
    Mlist_prime, ylist_prime = crt_prepare(pi_list_prime)
    rc_list_prime = list()
    for xi, Mi_prime, yi_prime in zip(x_list, Mlist_prime, ylist_prime):
        rc = xi * Mi_prime * yi_prime % N_prime
        rc_list_prime.append(rc)
    secret_from_share_missing1 = sum(rc_list_prime) % N_prime
    secret_from_share_missing1 = secret_from_share_missing1 % p0
    return secret_from_share_missing1


def reconst_from_rc(rc_list, N, p0):
    """
	Reconstruct the secret from rc_list.

	Input: rc_list, N, p0
	rc_list: list of random components.
	N: product of all modulis from rc_list.
	p0: size of the secret field.
	Output: secret
	secret: the recovered secret.
	"""

    secret = sum(rc_list)
    #print "secret_1", secret
    secret = secret % N
    #print "secret_2", secret
    secret = secret % p0
    return secret


def reconst_mod_p0(rc_list, N, p0):
    """
	Reconstruct the secret from rc_list_modp0.
	First modulo the rc_list by p0, then reconstruct the secret.

	Input: rc_list, N, p0
	rc_list: list of random components.
	N: product of all modulis from rc_list.
	p0: size of the secret field.
	Output: secret_from_rcmodp0
	secret_from_rcmodp0: the recovered secret
	"""

    rc_modp0 = [rc % p0 for rc in rc_list]
    mul_factor = floor(sum(rc_list) / N)
    secret_from_rcmodp0 = (sum(rc_modp0) - (mul_factor * N) % p0 + p0) % p0
    return secret_from_rcmodp0


def update_rc(rc_list, pi_list, N):
    """
	Update the rc_list to rc_list_prime.

	Input: rc_list, pi_list, N
	rc_list: the list of random components of size m.
	pi_list: the corresponding modulis of the participants.
	N: the product of all modulis
	Output: rc_list_prime
	rc_list_prime: the updated list of random components of size (m-1).
	"""
    m = len(rc_list)
    Mlist, ylist = crt_prepare(pi_list)
    pi_list_prime = pi_list[:-1]
    plast = pi_list[-1]
    Mlist_prime, ylist_prime = crt_prepare(pi_list_prime)

   # print Mlist_prime
    #print ylist_prime
    #print plast
    N_prime = N / plast
    rc_list_prime = list()
    for i in range(m - 1):
        rc = rc_list[i]
        yi_inv = inverse_mod(ylist[i], N)
        rc = rc * yi_inv * ylist_prime[i] % N
        rc = rc / plast % N_prime
        rc_list_prime.append(rc)
    #print "rc_list", rc_list
    #print "rc_list_prime", rc_list_prime
    return rc_list_prime


def update_rc_missing1(rc_list, pi_list, N):
    """
	Update the rc_list to rc_list_prime.

	Input: rc_list, pi_list, N
	rc_list: the list of random components of size m.
	pi_list: the corresponding modulis of the participants.
	N: the product of all modulis
	Output: rc_list_prime
	rc_list_prime: the updated list of random components of size (m-1).
	"""
    m = len(rc_list)
    Mlist, ylist = crt_prepare(pi_list)
    pi_list_prime = pi_list[:-1]
    plast = pi_list[-1]
    Mlist_prime, ylist_prime = crt_prepare(pi_list_prime)

    #print Mlist_prime
    #print ylist_prime
    #print plast
    N_prime = N / plast
    rc_list_prime = list()
    xlist = list()
    for rc, pi in zip(rc_list[:-1], pi_list_prime):
        xi = rc % pi
        xlist.append(xi)
    for i in range(m - 1):
        rc = xi * Mlist_prime[i] * ylist_prime[i] % N_prime
        rc_list_prime.append(rc)
    #print "rc_list", rc_list
    #print "rc_list_prime in update_rc_missing1", rc_list_prime
    return rc_list_prime


def get_p0inverse_list(p0, p_list):
    """

    :param p0: a prime number p0
    :param p_list: n prime numbers (p1, ..., pn)
    :return p0_inv_list : a list (p0_1^{-1}, ..., p0_n^{-1}), they are the inverses of p0 modulo (p1, ..., pn)
    """
    p0_inv_list = [inverse_mod(p0, p) for p in p_list]
    return p0_inv_list


def delete_zero_rows(A):
    L = []
    for j in range(A.nrows()):
        if (A.row(j)).is_zero():
            L.append(j)
    deletedA = A.delete_rows(L)
    return deletedA


def test_basis(A, B, N):
    s = randint(0, N - 1)
    s = vector([s])
    v = A * s
    for j in range(v.length()):
        v[j] = v[j] % N
    z = B.solve_left(v)
    #print "z is ", z
    m = B.nrows()
    z = random_vector(ZZ, m)
    v = z * B
    A = A.change_ring(IntegerModRing(N))
    v = v.change_ring(IntegerModRing(N))
    s = A.solve_right(v)
    #print "s is ", s


def get_sij_list_k(rc_list_k, rij_list_k, Nij_list_k, pi_list_k, p0):
    k = len(rc_list_k)
    sij_list_k = list()
    for j in range(k):
        sij = (rc_list_k[j] - rij_list_k[j] * Nij_list_k[j] * p0) % pi_list_k[j]
        sij_list_k.append(sij)
    return sij_list_k


def run_enumerate(s, p0, t, n, user_list, result_file):
    #print "---------------------- begin run() -----------------------"
    #print "n = ", n
    #print "t = ", t
    #print "s = ", s
    #print "p0 = ", p0
    sharelist = share_gen(n, t, p0, s)
    #print sharelist

    p_list = [pi for (pi, si) in sharelist]
    #print "p_list is ", p_list
    H = reduce(lambda x, y: x * y, p_list[:t])
    secret_space = ceil(H / p0)

    #user_list = [1, 2, 3, 4, 5]
    rc_list, r_list, pi_list, N = gen_rc(sharelist, user_list, p0)
    #print "N = ", N
    p0_inv_list = get_p0inverse_list(p0, pi_list)
    #print "p0_inv_list is ", p0_inv_list
    # secret = reconst_from_share(sharelist, ulist, p0)
    # print "secret reconstructed from share is ", secret
    # print " "
    secret = reconst_from_rc(rc_list, N, p0)
    #print "secret reconstructed from RC is ", secret
    rc_list_k = rc_list[:-1]
    #print "rc_list_k is ", rc_list_k
    p0_inv_list_k = p0_inv_list[:-1]
    #print "p0_inv_list_k is ", p0_inv_list_k
    Nij_list, y_list = crt_prepare(pi_list)
    Nij_list_k = Nij_list[:-1]
    #print "Nij_list_k is ", Nij_list_k
    y_list_k = y_list[:-1]
    #print "y_list_k is ", y_list_k
    k = len(user_list) - 1
    pi_list_k = pi_list[:-1]
    #print "pi_list_k is", pi_list_k
    sij_list_k = get_sij_list_k(rc_list_k, r_list[:-1], Nij_list_k, pi_list_k, p0)
    #print "sij_list_k is ", sij_list_k
    s_crt = CRT_list(sij_list_k, pi_list_k)
    #print "s_crt is ", s_crt

    #Nprime = reduce(lambda x, y: x * y, pi_list_k)
    #print "Nprime = ", Nprime

    #print "secret_space is ", secret_space

    #prob = float(secret_space) / Nprime
    #print "prob = ", prob

    #approximated_candidate_count = p0 ** k * prob
    #print "approximated_candidate_count = ", approximated_candidate_count

    candidate_secret_list = [0] * p0
    Z_p0 = IntegerModRing(p0)
    candidate_count = 0

    for rij_list_k in (Z_p0 ** k).list():
        rij_list_k = list(rij_list_k.change_ring(ZZ))
        sij_list_k = get_sij_list_k(rc_list_k, rij_list_k, Nij_list_k, pi_list_k, p0)
        s_crt = CRT_list(sij_list_k, pi_list_k)
        if s_crt < secret_space:
            candidate_count += 1
            candidate_secret_list[s_crt % p0] += 1
            #print "s_crt is ", s_crt
            #print "rij_list_k is ", rij_list_k
            #print "sij_list_k is ", sij_list_k
            #print "pi_list_k is ", pi_list_k
        # print "s_crt is ", s_crt

    have_wrong_candidate = 0
    guess_correct = 0
    h_s_cIk_inner = 0.0

    if candidate_count != candidate_secret_list[s]:
        have_wrong_candidate = 1
        guess_secret = candidate_secret_list.index(max(candidate_secret_list))
        prob_list = [float(count) / candidate_count for count in candidate_secret_list]

        for prob in prob_list:
            if prob > 0:
                term = prob * log(prob, 2).n()
                h_s_cIk_inner += term
        h_s_cIk_inner = -1 * h_s_cIk_inner
        if guess_secret == secret:
            guess_correct = 1
        result_file.write('===================================================\r\n')
        result_file.write('secret s = {}\r\n'.format(s))
        result_file.write('guessed secret s\' = {}\r\n'.format(guess_secret))
        result_file.write('number of candidate secret solutions is {}\r\n'.format(candidate_count))
        result_file.write('candiate secret list is {}\r\n'.format(candidate_secret_list))
    return (have_wrong_candidate, guess_correct, h_s_cIk_inner)
    #print "candidate_count = ", candidate_count
    #print "candidate_secret_list is ", candidate_secret_list


def run_improved_enumerate(s, p0, t, n, user_list, result_file):
    #print "---------------------- begin run() -----------------------"
    #print "n = ", n
    #print "t = ", t
    #print "s = ", s
    #print "p0 = ", p0
    print 'user_list is ', user_list
    sharelist = share_gen(n, t, p0, s)
    #print sharelist

    p_list = [pi for (pi, si) in sharelist]
    #print "p_list is ", p_list
    H = reduce(lambda x, y: x * y, p_list[:t])
    secret_space = ceil(H / p0)

    #user_list = [1, 2, 3, 4, 5]
    rc_list, r_list, pi_list, N = gen_rc(sharelist, user_list, p0)
    #print "N = ", N
    p0_inv_list = get_p0inverse_list(p0, pi_list)
    #print "p0_inv_list is ", p0_inv_list
    # secret = reconst_from_share(sharelist, ulist, p0)
    # print "secret reconstructed from share is ", secret
    # print " "
    secret = reconst_from_rc(rc_list, N, p0)
    #print "secret reconstructed from RC is ", secret
    #rc_list_k = rc_list[:-1]
    rc_list_t = rc_list[:t]
    rc_list_remain = rc_list[t:-1]
    #print "rc_list_k is ", rc_list_k
    #p0_inv_list_k = p0_inv_list[:-1]
    #print "p0_inv_list_k is ", p0_inv_list_k
    Nij_list, y_list = crt_prepare(pi_list)
    #Nij_list_k = Nij_list[:-1]
    Nij_list_t = Nij_list[:t]
    Nij_list_remain = Nij_list[t:-1]
    #print "Nij_list_k is ", Nij_list_k
    #y_list_k = y_list[:-1]
    #print "y_list_k is ", y_list_k
    #k = len(user_list) - 1
    #pi_list_k = pi_list[:-1]
    #print 'pi_list_k ', pi_list_k
    pi_list_t = pi_list[:t]
    #print 'pi_list_t ', pi_list_t
    pi_list_remain = pi_list[t: -1]
    #print 'pi_list_remain ', pi_list_remain
    #print "pi_list_k is", pi_list_k
    #sij_list_k = get_sij_list_k(rc_list_k, r_list[:-1], Nij_list_k, pi_list_k, p0)
    #sij_list_t = get_sij_list_k(rc_list_t, r_list[:t], Nij_list_t, pi_list_t, p0)
    #print 'sij_list_k ', sij_list_k
    #print 'sij_list_t ', sij_list_t

    #print "sij_list_k is ", sij_list_k
    #s_crt_k = CRT_list(sij_list_k, pi_list_k)
    #s_crt_t = CRT_list(sij_list_t, pi_list_t)
    #print "s_crt_k is ", s_crt_k
    #print 's_crt_t is ', s_crt_t

    #Nprime = reduce(lambda x, y: x * y, pi_list_k)
    #print "Nprime = ", Nprime

    #print "secret_space is ", secret_space

    #prob = float(secret_space) / Nprime
    #print "prob = ", prob

    #approximated_candidate_count = p0 ** k * prob
    #print "approximated_candidate_count = ", approximated_candidate_count
    Z_p0 = IntegerModRing(p0)

    candidate_secret_list_t = [0] * p0
    candidate_count_t = 0
    for rij_list_t in (Z_p0 ** t).list():
        rij_list_t = list(rij_list_t.change_ring(ZZ))
        sij_list_t = get_sij_list_k(rc_list_t, rij_list_t, Nij_list_t, pi_list_t, p0)
        s_crt_t = CRT_list(sij_list_t, pi_list_t)
        if s_crt_t < secret_space:
            rij_list_remain = list()
            for (rci, pi, Ni) in zip(rc_list_remain, pi_list_remain, Nij_list_remain):
                rij = (rci - s_crt_t) * inverse_mod(p0*Ni, pi) % pi
                rij_list_remain.append(rij)
            if all(rij < p0 for rij in rij_list_remain):
                print 's_crt_t = ', s_crt_t
                print 'rij_list_t ', rij_list_t + rij_list_remain
                candidate_count_t += 1
                candidate_secret_list_t[s_crt_t % p0] += 1
    print 'candidate_count_t = ', candidate_count_t
    print 'candidata_secret_list_t is'
    print candidate_secret_list_t

    have_wrong_candidate = 0
    guess_correct = 0
    h_s_cIk_inner = 0.0

    if candidate_count_t != candidate_secret_list_t[s]:
        have_wrong_candidate = 1
        guess_secret = candidate_secret_list_t.index(max(candidate_secret_list_t))
        prob_list = [float(count) / candidate_count_t for count in candidate_secret_list_t]

        for prob in prob_list:
            if prob > 0:
                term = prob * log(prob, 2).n()
                h_s_cIk_inner += term
        h_s_cIk_inner = -1 * h_s_cIk_inner
        if guess_secret == secret:
            guess_correct = 1
        result_file.write('===================================================\r\n')
        result_file.write('secret s = {}\r\n'.format(s))
        result_file.write('guessed secret s\' = {}\r\n'.format(guess_secret))
        result_file.write('number of candidate secret solutions is {}\r\n'.format(candidate_count_t))
        result_file.write('candiate secret list is {}\r\n'.format(candidate_secret_list_t))
    return (have_wrong_candidate, guess_correct, h_s_cIk_inner)

def main_enumerate(m, result_file):
    times = 10
    num_of_non_unique_solution = 0
    num_of_guess_correct = 0
    h_s_CIk = 0.0
    p0 = 5
    n = 10
    t = 4
    full_user_set = set(range(1, n + 1))
    actual_user_set = Subsets(full_user_set, m)


    for j in xrange(times):
        user_set = actual_user_set.random_element()
        user_list = list(user_set)   #userlist: m users join the reconstruction phase
        #print 'user_list is '
        #print user_list
        s = randint(0, p0-1)
        nonunique_solution, guess_correct, h_s_CIk_inner = run_improved_enumerate(s, p0, t, n, user_list,result_file)
        num_of_non_unique_solution += nonunique_solution
        num_of_guess_correct += guess_correct
        h_s_CIk += h_s_CIk_inner

    h_s_CIk = h_s_CIk / times
    print '{} out of {} have non unique solution'.format(num_of_non_unique_solution, times)
    print '{} out of {} have correct guessed secret'.format(num_of_guess_correct, num_of_non_unique_solution)
    print 'The conditional entropy H(s|C_Ik) = ', h_s_CIk
    #result_file.write('{} out of {} have non unique solution\r\n'.format(num_of_non_unique_solution, times))
    #result_file.write('{} out of {} have correct guessed secret\r\n'.format(num_of_guess_correct, num_of_non_unique_solution))
    #result_file.write('The conditional entropy H(s|C_Ik) ={}\r\n'.format(h_s_CIk))
    return (times - num_of_non_unique_solution, num_of_guess_correct, h_s_CIk)





def CRT_test(m, times=10):
    n = 10
    t = 4
    p0 = 5
    outfile = 'm_equals_' + str(m) + '_CRTGOSS' + '.txt'
    result_file = open(outfile, 'w+')
    result_file.write('CRTGOSS Results\r\n')
    result_file.write('Number os users: n = {}\r\n'.format(n))
    result_file.write('Threshold: t = {}\r\n'.format(t))
    result_file.write('Secret size: p0 = {}\r\n'.format(p0))
    result_list = [main_enumerate(m, result_file) for _ in xrange(times)]
    unique_solution_list = [result[0] for result in result_list]
    correct_guess_list = [result[1] for result in result_list]
    conditional_entropy_list = [result[2] for result in result_list]
    #print 'unique_solution_list is.'
    #print unique_solution_list
    #print 'correct_guess_list is.'
   # print correct_guess_list
    #print 'conditional_entropy_list is.'
    #print conditional_entropy_list
    result_file.write('unique_solution_list is.\r\n')
    for result in result_list:
        result_file.write('{} '.format(result[0]))
    result_file.write('\r\ncorrect_guess_list is.\r\n')
    for result in result_list:
        result_file.write('{} '.format(result[1]))
    result_file.write('\r\nconditional_entropy_list is.\r\n')
    for result in result_list:
        result_file.write('{} '.format(result[2]))
    result_file.close()
    return result_list

def get_CRT_data():
    number_of_success_list = [CRT_test(m) for m in xrange(5, 11)]
    CRT_data = np.array(number_of_success_list)
    for (j, number_of_success) in enumerate(number_of_success_list):
        np.savetxt('crt_data.txt' + str(5 + j), number_of_success)
    return CRT_data

CRT_data = get_CRT_data()
print CRT_data

#s = 3
#p0 = 5
#t = 4
#n = 10
#user_list = [1, 2, 7, 4, 5, 6]
#run_improved_enumerate(s, p0, t, n, user_list)
