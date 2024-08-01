/**
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
*/
#include <lean/lean.h>
#include <fcntl.h>
#include <unistd.h>
#include <random>

#include <stdio.h> // Profiling only

#ifdef __APPLE__
    std::random_device generator;
#else
    std::mt19937_64 generator(time(NULL));
#endif

// Set via enviornment variable?
static bool PROFILE_FFI_CALLS = true;
int FFI_LOG;


extern "C" lean_object * prob_UniformByte (lean_object * eta) {
    lean_dec(eta);
    unsigned char r;
    int urandom = open("/dev/urandom", O_RDONLY | O_CLOEXEC);
    if (urandom == -1) {
        lean_internal_panic("prob_UniformByte: /dev/urandom cannot be opened");
    }
    read(urandom, &r,1);
    close(urandom);
    return lean_box((size_t) r);
}


extern "C" lean_object * prob_UniformP2(lean_object * a, lean_object * eta) {
    if (PROFILE_FFI_CALLS) {
        char message[100];
        if (lean_is_scalar(a)) {
            size_t n = lean_unbox(a);
            snprintf(message, 100, "%lu\n", n);
        } else {
            lean_internal_panic("Large boxed number");
        }
        write(FFI_LOG, message, strlen(message));
    }

    lean_dec(eta);
    if (lean_is_scalar(a)) {
        size_t n = lean_unbox(a);
        if (n == 0) {
            lean_internal_panic("prob_UniformP2: n == 0");
        } else {
            int lz = std::__countl_zero(n);
            int bitlength = (8*sizeof n) - lz - 1;
            size_t bound = 1 << bitlength; 
            std::uniform_int_distribution<size_t> distribution(0,bound-1);
            size_t r = distribution(generator);
            lean_dec(a); 
            return lean_box(r);
        }
    } else {
        lean_object * res = lean_usize_to_nat(0);
        do {
            a = lean_nat_sub(a,lean_box(LEAN_MAX_SMALL_NAT));
            std::uniform_int_distribution<size_t> distribution(0,LEAN_MAX_SMALL_NAT-1);
            size_t rdm = distribution(generator);
            lean_object * acc = lean_usize_to_nat(rdm);
            res = lean_nat_add(res,acc);
        } while(lean_nat_le(lean_box(LEAN_MAX_SMALL_NAT),a));
        lean_object * rem = prob_UniformP2(a,lean_box(0));
        return lean_nat_add(res,rem);
    }
}

extern "C" lean_object * prob_Pure(lean_object * a, lean_object * eta) {
    lean_dec(eta);
    return a;
} 

extern "C" lean_object * prob_Bind(lean_object * f, lean_object * g, lean_object * eta) {
    lean_dec(eta);
    lean_object * exf = lean_apply_1(f,lean_box(0));
    lean_object * pa = lean_apply_2(g,exf,lean_box(0));
    return pa;
} 

extern "C" lean_object * prob_While(lean_object * condition, lean_object * body, lean_object * init, lean_object * eta) {
    lean_dec(eta);
    lean_object * state = init; 
    lean_inc(state);
    lean_inc(condition);
    uint8_t cond = lean_unbox(lean_apply_1(condition,state));
    while (cond) {
        lean_inc(body);
        state = lean_apply_2(body,state,lean_box(0));
        lean_inc(condition);
        lean_inc(state);
        cond = lean_unbox(lean_apply_1(condition,state));
    }
    return state;
}

extern "C" lean_object * my_run(lean_object * a) {
    if (PROFILE_FFI_CALLS) {
        remove("./uniform_samples_prof");
        FFI_LOG = open("./uniform_samples_prof", O_WRONLY | O_CREAT | O_EXCL, 0777);
        if (FFI_LOG < 0) {
            lean_internal_panic("FFI_LOG: Error opening log file");
        }
    }

    lean_object * comp = lean_apply_1(a,lean_box(0));
    lean_object * res = lean_io_result_mk_ok(comp);

    if (PROFILE_FFI_CALLS) {
        close(FFI_LOG);
    }
    return res;
} 

extern "C" uint32_t dirty_io_get(lean_object * a) {
    lean_object * r1 = lean_apply_1(a,lean_box(0));
    lean_object * r2 = lean_io_result_get_value(r1);
    if (lean_is_scalar(r2)) {
        size_t r3 = lean_unbox(r2);
        return r3;
    } else {
        lean_internal_panic("dirty_io_get: value not scalar");
    }
}
