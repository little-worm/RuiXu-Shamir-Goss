# -*- coding: utf-8 -*-
"""
Created on Sat Aug 10 23:33:41 2019

@author: thinkpad
"""
import matplotlib.pyplot as plt
import numpy as np


def load_data():
	enumerate_data = np.loadtxt('enumerate_data.txt')
	lwe_data = np.loadtxt('LWE_data.txt')
	return enumerate_data, lwe_data

def process_data(enumerate_data, lwe_data):
    print('enumerate_data shpa is {}'.format(enumerate_data.shape))
    enumerate_data = np.delete(enumerate_data, 2, axis=1)
    print('enumerate_data shpa is {}'.format(enumerate_data.shape))
    enumerate_data = np.sum(enumerate_data, axis=1)
    print('enumerate_data shpa is {}'.format(enumerate_data.shape))
    print('enumerate_data is')
    print(enumerate_data)
    enumerate_mean = np.mean(enumerate_data)
    enumerate_std = np.std(enumerate_data)
    lwe_mean = np.mean(lwe_data, axis=1)
    lwe_std = np.std(lwe_data, axis=1)
    plot_mean = np.append(enumerate_mean, lwe_mean) / 1000
    plot_std = np.append(enumerate_std, lwe_std) / 1000
    return (plot_mean, plot_std)

#x = np.array([4, 5, 6, 7, 8, 9])

#plot_mean = np.array([ 0.8815 ,  0.04551,  0.22446,  0.81544,  0.99968,  1.     ])

#plot_std = np.array([ 0.0100025 ,  0.00618788,  0.01390785,  0.01182482,  0.00054553,  0.        ])

#fig = plt.figure()
#ax = fig.add_axes([0.1, 0.1, 0.8, 0.8])
#ax.set_xlim(3.9, 9.1)
#ax.set_ylim(0, 1.1)
#ax.errorbar(x, plot_mean, 3 * plot_std, linestyle='none', marker='o', capsize=3, markersize=1.2)

#plt.savefig('plot1.pdf')

def plot_shamirGOSS(plot_mean, plot_std):
    x = np.array([4, 5, 6, 7, 8, 9])
    fig = plt.figure()
    ax = fig.add_axes([0.1, 0.1, 0.8, 0.8])
    
    ax.errorbar(x, plot_mean, plot_std, linestyle='none', marker='o', capsize=3, markersize=2.2, color='r')
    ax.set_xlim(3.9, 9.1)
    ax.set_ylim(0, 1.1)
    plt.xlabel('number of RCs: $k$')
    plt.ylabel('success probability')
    #plt.title('Success probability of adversary')
    fig.savefig('shamirGOSS.pdf')
    fig.show()


enumerate_data, lwe_data = load_data()
plot_mean, plot_std = process_data(enumerate_data, lwe_data)
plot_shamirGOSS(plot_mean, plot_std)