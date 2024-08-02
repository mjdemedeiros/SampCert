# Profiling script for SampCert's uniform sampler

import subprocess
import numpy as np
import matplotlib.pyplot as plt
import tqdm as tqdm

def gauss_sample_data(num, den, mix):
    cmd = ['./.lake/build/bin/check', str(num), str(den), str(mix)]
    subprocess.Popen(cmd).wait()
    samples = (np.genfromtxt("uniform_samples_prof", dtype="int"))
    unique, counts = np.unique(samples, return_counts=True)
    return unique, counts

def merge_samples(us, cs):
    merged_values = np.unique(np.concatenate(us))
    merged_counts = np.zeros(merged_values.size, np.int64)
    for (u, c) in zip(us, cs):
        for (v, ct) in zip(u, c):
            merged_counts[np.where(merged_values == v)[0][0]] += ct
    return merged_values, merged_counts

def run_sample_set(N, num, den, mix, norm=True):
    values = []
    counts = []
    for i in tqdm.tqdm(range(0, N), desc="({},{},{})".format(num, den, mix), leave=False):
        u, c = gauss_sample_data(num, den, mix)
        values += [u]
        counts += [c]
    ms, mc = merge_samples(values, counts)
    ms = np.array(ms)
    mc = np.array(mc)
    if norm:
        mc = mc / np.sum(mc)
    return ms, mc

# Histogram for a single parameter set
def plot_sample_set(N, num, den, mix, out="test.pdf"):
    sizes, counts = run_sample_set(N, num, den, mix, norm=False)
    norm_counts = counts / np.sum(counts)
    mean_total_calls = np.sum(counts) / float(N)
    plt.figure(figsize=(10,6))
    plt.title("{} x discreteGaussianSample({}, {}, {}); mean total calls: {}".format(N, num, den, mix, mean_total_calls))
    plt.plot(sizes, norm_counts, color="orange", marker='.')
    plt.xlabel("Uniform Sample Size")
    plt.ylabel("Number of calls")
    # print("Max call size: {}".format(np.max(sizes)))
    # print("Number of max calls: {}".format(counts[np.argmax(sizes)]))
    plt.savefig(out)


if __name__ == "__main__":
    # for j in tqdm.tqdm(range(0, 2)):
    #     a, b = run_sample_set(100, 1, 1, j, norm=False)
    plot_sample_set(100, 1, 1, 1, out="1.pdf")
    plot_sample_set(100, 5, 5, 1, out="5.pdf")
    plot_sample_set(100, 10, 10, 1, out="10.pdf")
