from sage.all import *
from operator import mul
from fpylll import IntegerMatrix
from fpylll import LLL
from fpylll import CVP
import numpy as np
#from math import log
import profile

def sharegen(s, q, p, t, n):
	'''

	:param s: the secret, an element of F_q
	:param q: a prime number, indicating the secret size
	:param p: a prime number with p > q + n q^2, indicating the share size
	:param t: an integer, the threshold of the secret sharing scheme
	:param n: an integer, n > t, the number of players in the secret sharing scheme
	:return (s_1, ..., s_n): a tuple of n element, s_i = (x_i, f(x_i)) and f(x_i) belongs to F_p, is the share of user i
	:return vec_az: (s, a1, ..., a_{t-1}): an integer vector of t element, s is the secret, a_i is the polynomial coefficient
	'''

	if p < n:
		exit('p should be greater than n')

	Fp = IntegerModRing(p)
	Fx = PolynomialRing(Fp, 'x')
	s = Fp(s)
	vec_a = random_vector(Fp, t)
	vec_a[0] = s
	vec_az = vec_a.change_ring(ZZ)
	x = var('x')
	f = sum([b * x ** a for a, b in enumerate(vec_az)])
	f = Fx(f)
	user_list = [Fp(u) for u in range(1, n + 1)]
	share_list = list()
	for xi in user_list:
		fxi = f(x=xi)
		share_list.append((xi, fxi))
	return (share_list,vec_a)

def compute_lm(user_list, p):
	"""

	:param user_list: (x_1, ..., x_m) the list of m users, each user is identified by xi (an integer)
	:param p: a prime number with p > q + n q^2, indicating the share size
	:return: lm_list: a list of the Largrange coefficients, each element l_mj = \prod_{v=1,v\ne j}^{m}\frac{x_iv}{x_iv -
	        x_ij} for j = 1, ..., m
	"""
	Fp = IntegerModRing(p)
	user_list_mod_p = [Fp(user) for user in user_list]
	lm_list = list()
	for xj in user_list_mod_p:
		user_list_mod_p_without_xj = [user - xj for user in user_list_mod_p]
		user_list_mod_p_without_xj = [user for user in user_list_mod_p_without_xj if user != 0]
		numerator = reduce(mul, user_list_mod_p) / xj
		denominator = reduce(mul, user_list_mod_p_without_xj)
		lmj = numerator / denominator
		lm_list.append(lmj)
	return lm_list


def rcgen(share_list, user_list, q, p):
	"""
	:param share_list: the share of n users, each user's share is (xi, fxi) \in F_p^2
	:param user_list: (x_1, ..., x_m) the list of m users, each user is identified by xi \in [n]
	:param q: a prime number, indicating the secret size
	:param p: a prime number with p > q + n q^2, indicating the share size
	:return: rc_list: (rc_1, ..., rc_m) the list of m randomized components, each rc_i belongs to F_p
	:return: random_list: (r_1, ..., r_m) the list of m random components, each r_i belongs to F_q
	:return: lm_list: (lm_1, ..., lm_m) the list of m Largrange coefficients, each lm_j = l_mj = \prod_{v=1,v\ne j}^{m}
	         \frac{x_iv}{x_iv - x_ij} each lm_j belongs to F_p
	"""

	Fp = IntegerModRing(p)
	Fq = IntegerModRing(q)
	m = len(user_list)
	q = Fp(q)
	rc_list = list()
	lm_list = compute_lm(user_list, p)
	random_vect = random_vector(Fq, m)  #type: vector in Fq of size m
	random_vect = random_vect.change_ring(Fp)  # type: vector in Fp of size m
	random_list = list(random_vect)
	for j, user in enumerate(user_list):
		#print 'user = ', user
		xi, fxi = share_list[user - 1]
		#print 'xi, fxi = ', xi, fxi
		ci = fxi * lm_list[j] +random_list[j] * q
		rc_list.append(ci)
	return (rc_list, random_list, lm_list)


def reconstruct(rc_list, q, p):
	"""

	:param rc_list: (rc1, ..., rc_m) the list of m random components, each element is in Fp
	:param p: a prime number with p > q + n q^2, indicating the share size
	:param q: a prime number, indicating the secret size
	:return: s: the shared secret in Fq
	"""
	Fq = IntegerModRing(q)
	secret = sum(rc_list)
	secret = Fq(secret)

	return(secret)

def my_vandermonde(v, ncols=None, ring=None):
	def entries(i, j):
		return v[i]**j
	if ncols is None:
		ncols = len(v)
	return matrix(entries, nrows=len(v), ncols=ncols, ring=ring)


def get_LWEA(q, lm_list, user_list, p, t):
	"""
	Get the matrix A for the LWE problem as A*s + E = C
	:param q: a prime number, indicating the secret size
	:param lm_list: (lm_1, ..., lm_k) the list of k Largrange coefficients, each lm_j = l_mj = \prod_{v=1,v\ne j}^{m}
	         \frac{x_iv}{x_iv - x_ij} each lm_j belongs to F_p
	:param user_list: user_list: (x_1, ..., x_k) the list of k users, each user is identified by xi \in [n]
	:param p: a prime number with p > q + n q^2, indicating the share size
	:param t: an integer indicating the threshold in the secret sharing scheme
	:return: A: a matrix for the LWE problem as A*s + E = C, A is over Fp
	"""
	Fp = IntegerModRing(p)
	q = Fp(q) # express q in the filed F_p
	q_inv = 1 / q
	k = len(user_list) # k is the number of RCs the adversary sees
	x = [Fp(xi) for xi in user_list] # list of (x_{i_1}, ..., x_{i_k}) each x_i is a user identifier
	#A = matrix(Fp, k, t) # matrix over Fp with size k x t
	A = my_vandermonde(x, ncols=t) # non square Vandermonde matrix of size k x t, each row is (1, x_i, ..., x_i^{t-1})
	for i in range(k):
		A[i] *= lm_list[i]
	A *= q_inv
	return A

def get_LWEC(q, rc_list, p):
	"""

	:param q: a prime number, indicating the secret size
	:param rc_list: (rc1, ..., rc_k) the list of k random components, each element is in Fp
	:param p: a prime number with p > q + n q^2, indicating the share size
	:return C: a vector of (c_1, ..., c_k) for the LWE problem as A*S + E = C. Each element c_i = q^{-1} rc_i, C is over Fp.
	"""
	Fp = IntegerModRing(p)
	q = Fp(q)
	q_inv = 1 / q
	C = vector(Fp, rc_list)
	C *= q_inv
	return C


def delete_zero_rows(A):
	"""

	:param A: a matrix with zero rows in the end
	:return deletedA: a matrix without the zero rows
	"""
	L = []
	for j in range(A.nrows()):
		if (A.row(j)).is_zero():
			L.append(j)
	deletedA = A.delete_rows(L)
	return deletedA


def compute_basis(LWEA, p):
	"""

	:param LWEA: the LWE matrix A \in Fp^{k x t}
	:param p: a prime number, indicating the share size
	:return basis: basis of the lattice L_{A,p} = {y \in Z_p^k | y = Ax (mod p) for some x \in Z^t}
	:type Sage matrix
	"""
	k = LWEA.nrows()
	t = LWEA.ncols()
	LWEA_Z = LWEA.change_ring(ZZ)
	LWEA_ZT = LWEA_Z.transpose()
	pidenmat = identity_matrix(ZZ, k) * p
	blockmat = block_matrix([LWEA_ZT, pidenmat], ncols=1)
	prebasis = blockmat.echelon_form()
	basis = delete_zero_rows(prebasis)
	#print 'basis is'
	#print basis
	return basis

def run_LWE(s, q, t, n, userlist):

	p = next_prime(q + n * q ** 2)
	Fq = IntegerModRing(q)
	Fp = IntegerModRing(p)
	print 'p = ', p
	print 's = ', s
	#userlist = [1, 2, 3, 4, 5, 6, 7]
	#userlist = [9, 2, 3, 4, 5, 6, 7, 8, 1]
	sharelist, vec_s = sharegen(s, q, p, t, n)
	#print 'sharelist is ', sharelist
	#print 'vec_s is ', vec_s
	#print 'type of vec_s is ', type(vec_s)
	rclist, randomlist, lmlist = rcgen(sharelist, userlist, q, p)
	#print 'rclist is ', rclist
	#print 'rclist type is ', type(rclist)
	#print 'randomlist is ', randomlist
	#print 'randomlist type is ', type(randomlist)
	randomvec = vector(Fp, randomlist)
	#print 'lmlist is ', lmlist
	secret = reconstruct(rclist, q, p)
	#print 'the secret reconstructed is ', secret
	lmlist_k = lmlist[:-1]
	userlist_k = userlist[:-1]
	rclist_k = rclist[:-1]
	randomvec_k = randomvec[:-1]
	A = get_LWEA(q, lmlist_k, userlist_k, p, t)
	C = get_LWEC(q, rclist_k, p)
	#print 'LWEA is'
	#print A
	#print 'LWEA type is ', type(A)
	#print 'LWEC is'
	#print C
	#print 'LWEC type is ', type(C)
	#Cprime = A * vec_s + randomvec_k
	#print 'Cprime is '
	#print Cprime
	basis = compute_basis(A, p)
	#print 'basis is'
	#print basis
	#print 'basis has type ', type(basis)
	#LWEB_sage = matrix(LWEB)
	#LWEB = LWEB.transpose()

	k = A.nrows()
	t = A.ncols()
	#z_rand = random_vector(ZZ, k)
	#lattice_vec = z_rand * basis

	#print 'z_rand is ', z_rand
	#print 'lattice_vec is ', lattice_vec

	#lattice_vec = lattice_vec.change_ring(Fp)
	#x = A.solve_right(lattice_vec)
	#print 'x is ', x

	LWEB_fpylll = IntegerMatrix.from_matrix(basis)
	#print 'LWEB_fpylll is'
	#print LWEB_fpylll
	lll = LLL.reduction(LWEB_fpylll)
	#print 'LWEB_fpylll after LLL reduction is'
	#print LWEB_fpylll
	C = C.change_ring(ZZ)
	closest_vec = CVP.closest_vector(LWEB_fpylll, C)
	#print 'closest_vec is ', closest_vec
	#print 'closest_vec has type ', type(closest_vec)
	closest_vec = vector(Fp, closest_vec)
	#error_vec = C - closest_vec
	#print 'error vector is'
	#print error_vec
	#print 'randomlist is'
	#print randomlist
	recovered_s = A.solve_right(closest_vec)
	#print 'recovered_s is'
	#print recovered_s
	#print 'vec_s is'
	#print vec_s
	have_wrong_candidate = 0
	if recovered_s[0] != s:
		#print 'error'
		have_wrong_candidate = 1
	return have_wrong_candidate

def main_LWE(m, result_file):
	times = 1000
	q = 5
	n = 10
	t = 4

	full_user_set = set(range(1, n + 1))
	actual_user_set = Subsets(full_user_set, m)
	#result_file.write('ShamirGOSS when k > t\r\n')
	#result_file.write('Number of users: n = {}\r\n'.format(n))
	#result_file.write('Threshold: t = {}\r\n'.format(t))
	#result_file.write('Secret size q = {}\r\n'.format(q))
	num_of_non_unique_solution = 0
	for j in xrange(times):
		user_set = actual_user_set.random_element()
		user_list = list(user_set)   #userlist: m users join the reconstruction phase
		print 'user_list is '
		print user_list
		s = randint(0, q-1)
		num_of_non_unique_solution += run_LWE(s, q, t, n, user_list)
	print '{} out of {} have non unique solution'.format(num_of_non_unique_solution, times)
	#result_file.write('{} out of {} have non unique solution\r\n'.format(num_of_non_unique_solution, times))
	return (times - num_of_non_unique_solution)

def run_enumerate(s, q, t, n, userlist, result_file):
	p = next_prime(q + n * q ** 2)
	Fp = IntegerModRing(p)
	Fq = IntegerModRing(q)
	#print 'p = ', p
	#userlist = [1, 2, 3, 4, 5, 6, 7]


	sharelist, vec_s = sharegen(s, q, p, t, n)
	#print 'sharelist is ', sharelist
	#print 'vec_s is ', vec_s
	#print 'type of vec_s is ', type(vec_s)
	rclist, randomlist, lmlist = rcgen(sharelist, userlist, q, p)
	#print 'rclist is ', rclist
	#print 'rclist type is ', type(rclist)
	#print 'randomlist is ', randomlist
	#print 'randomlist type is ', type(randomlist)
	randomvec = vector(Fp, randomlist)
	#print 'lmlist is ', lmlist
	secret = reconstruct(rclist, q, p)
	#print 'the secret reconstructed is ', secret
	lmlist_k = lmlist[:-1]
	userlist_k = userlist[:-1]    #userlist_k: k users whose RCs will be observed by the adversary
	rclist_k = rclist[:-1]        #k RCs observed by the adversary
	randomvec_k = randomvec[:-1]
	A = get_LWEA(q, lmlist_k, userlist_k, p, t)   #A is the matrix X in our paper
	C = get_LWEC(q, rclist_k, p)                  #C is C in our paper
	#print 'LWEA is'
	#print A
	#print 'LWEA type is ', type(A)
	#print 'LWEC is'
	#print C
	#print 'LWEC type is ', type(C)
	#Cprime = A * vec_s + randomvec_k
	#print 'Cprime is '
	#print Cprime
	#basis = compute_basis(A, p)
	#print 'basis is'
	#print basis
	#print 'basis has type ', type(basis)


	#LWEB_sage = matrix(LWEB)
	#LWEB = LWEB.transpose()

	k = A.nrows()    # number of RCs adversary can see
	t = A.ncols()    # threshold of secret sharing scheme

	candidate_solution_count = 0
	candidate_secret_list = [0] * q

	for rand_enum in (Fq ** k).list():    #enumerate all possible (r_i1, ..., r_ik)
		rand_enum = rand_enum.change_ring(Fp)
		candidate_sol = A.solve_right(C - rand_enum)   #the solution of equation A*s + r = C
		if candidate_sol[0] < q:                     # if the first element of the solution is less than q
			candidate_solution_count += 1
			candidate_secret_list[candidate_sol[0]] += 1
			#print 'candidate_sol is ', candidate_sol
			#print 'rand_enum is ', rand_enum
	print 'secret s = ', s
	print 'number of candidate solutions is ', candidate_solution_count
	print 'candidate secret list is ', candidate_secret_list
	have_wrong_candidate = 0
	guess_correct = 0
	h_s_cIk_inner = 0.0
	if candidate_solution_count != candidate_secret_list[s]:
		have_wrong_candidate = 1
		guess_secret = candidate_secret_list.index(max(candidate_secret_list))
		prob_list = [float(count) / candidate_solution_count for count in candidate_secret_list]

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
		result_file.write('number of candidate secret solutions is {}\r\n'.format(candidate_solution_count))
		result_file.write('candiate secret list is {}\r\n'.format(candidate_secret_list))

	return (have_wrong_candidate, guess_correct, h_s_cIk_inner)



#print euler_phi(13)
def main_enumerate(result_file):
	times = 1000
	num_of_non_unique_solution = 0
	num_of_guess_correct = 0
	h_s_CIk = 0.0
	q = 5
	n = 10
	t = 4
	m = t + 1
	full_user_set = set(range(1, n + 1))
	actual_user_set = Subsets(full_user_set, m)


	for j in xrange(times):
		user_set = actual_user_set.random_element()
		user_list = list(user_set)   #userlist: m users join the reconstruction phase
		print 'user_list is '
		print user_list
		s = randint(0, q-1)
		nonunique_solution, guess_correct, h_s_CIk_inner = run_enumerate(s, q, t, n, user_list, result_file)
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

#run_LWE()
#run_enumerate(2, 5, 4, 10, [1, 3, 4, 6, 7])



def enumerate_test(times=100):
	q = 5
	n = 10
	t = 4
	m = t + 1
	outfile = 'shamirGOSS_k_equals_t.txt'
	result_file = open(outfile, 'w+')
	result_file.write('ShamirGOSS when k = t\r\n')
	result_file.write('Number of users: n = {}\r\n'.format(n))
	result_file.write('Threshold: t = {}\r\n'.format(t))
	result_file.write('Secret size q = {}\r\n'.format(q))
	result_list = [main_enumerate(result_file) for _ in xrange(times)]
	unique_solution_list = [result[0] for result in result_list]
	correct_guess_list = [result[1] for result in result_list]
	conditional_entropy_list = [result[2] for result in result_list]
	print 'unique_solution_list is.'
	print unique_solution_list
	print 'correct_guess_list is.'
	print correct_guess_list
	print 'conditional_entropy_list is.'
	print conditional_entropy_list
	result_file.write('unique_solution_list is.\r\n')
	for result in result_list:
		result_file.write('{} '.format(result[0]))
	result_file.write('\r\ncorrect_guess_list is.\r\n')
	for result in result_list:
		result_file.write('{} '.format(result[1]))
	result_file.write('\r\nconditional_entropy_list is.\r\n')
	for result in result_list:
		result_file.write('{} '.format(result[2]))
	main_enumerate(result_file)
	result_file.close()
	return result_list


def LWE_test(m, times=100):
	q = 5
	n = 10
	t = 4
	outfile = 'm_equals_' + str(m) + '_shamirGOSS_k_larger_than_t' + '.txt'
	result_file = open(outfile, 'a+')
	result_file.write('ShamirGOSS when k > t\r\n')
	result_file.write('Number of users: n = {}\r\n'.format(n))
	result_file.write('Threshold: t = {}\r\n'.format(t))
	result_file.write('Secret size q = {}\r\n'.format(q))
	unique_solution_list = [main_LWE(m, result_file) for _ in xrange(times)]
	result_file.write('The list of number of non unique solution is.\r\n')
	for unique_solution_count in unique_solution_list:
		result_file.write('{} '.format(unique_solution_count))
	result_file.close()
	return unique_solution_list

def get_LWE_data():
	number_of_success_list = [LWE_test(m) for m in xrange(6, 11)]
	LWE_data = np.array(number_of_success_list)
	return LWE_data

def get_enumerate_data():
	times = 10
	result_list = enumerate_test(times)
	enumerate_data = np.array(result_list)
	return enumerate_data


def collect_data():
	x1 = '40 44 41 41 35 48 38 39 47 40 37 47 39 47 46 40 41 43 55 45 42 51 41 53 47 37 43 44 38 51 51 44 45 47 37 45 57 45 53 55 50 35 44 36 34 58 37 46 48 50 48 37 62 53 29 44 45 47 52 42 44 49 46 48 48 47 48 42 53 55 47 34 43 36 53 46 51 44 46 42 40 54 54 42 45 56 40 46 50 46 53 47 56 36 43 49 47 51 47 51'
	x2 = '224 217 223 235 203 237 222 204 225 222 214 232 219 217 217 226 217 194 224 236 216 215 217 224 218 226 229 231 222 244 225 281 244 206 222 197 241 216 208 211 213 231 228 224 229 213 228 222 207 226 216 239 225 221 242 229 210 256 222 222 209 211 229 230 231 241 201 238 223 240 237 219 217 226 245 211 200 238 217 238 212 221 251 196 222 219 228 208 240 230 229 240 250 238 231 213 230 206 244 233'
	x3 = '798 817 811 804 810 837 821 779 809 817 819 798 803 833 819 827 823 824 823 814 829 812 814 805 813 807 843 816 819 827 809 810 800 824 824 807 813 822 805 805 836 836 825 800 787 824 810 791 833 813 812 809 807 823 815 816 807 827 826 821 806 800 818 811 818 814 816 810 810 820 823 813 829 825 832 825 838 806 839 833 802 813 808 805 826 811 818 807 818 810 811 794 809 831 796 809 826 814 834 808'
	x4 = '999 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 999 998 1000 999 1000 1000 1000 1000 1000 1000 999 1000 1000 999 999 1000 1000 1000 999 1000 999 999 999 1000 1000 1000 1000 1000 1000 999 999 999 1000 999 999 1000 998 1000 1000 999 1000 999 1000 1000 1000 1000 1000 1000 1000 1000 999 1000 1000 998 1000 998 1000 1000 1000 999 1000 999 1000 1000 999 1000 1000 1000 1000 1000 999 999 1000 1000 1000 999 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000'
	x5 = '1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000 1000'
	x1 = [int(x) for x in x1.split()]
	x2 = [int(x) for x in x2.split()]
	x3 = [int(x) for x in x3.split()]
	x4 = [int(x) for x in x4.split()]
	x5 = [int(x) for x in x5.split()]
	LWE_data = np.array([x1, x2, x3, x4, x5])
	np.savetxt('LWE_data.txt', LWE_data)
	print LWE_data

def load_data():
	enumerate_data = np.loadtxt('enumerate_data.txt')
	LWE_data = np.loadtxt('LWE_data.txt')
	print enumerate_data
	print LWE_data
	return enumerate_data, LWE_data

#()
#collect_data()
LWE_data = get_LWE_data()
print LWE_data
np.savetxt('LWE_data.txt', LWE_data)

enumerate_data = get_enumerate_data()
print enumerate_data
np.savetxt('enumerate_data.txt', enumerate_data)

#LWE_test(6, 10)
#enumerate_test()
