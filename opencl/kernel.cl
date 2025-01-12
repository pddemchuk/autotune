kernel void sum_even(global int *glob, global int *output, local int *loc, int TS) {
    int my_elem = get_local_id(0);
    // MAP
    loc[my_elem] = 0;
    int sum = 0;
    for (int i = 0; i < TS; i++) {
        int idx = i + get_global_id(0) * TS;
        if (glob[idx] % 2 == 0)
            sum += glob[idx];
    }
    loc[my_elem] = sum;
    barrier (CLK_LOCAL_MEM_FENCE);
    // REDUCE local
    if (my_elem == 0) {
        for (int i = 0; i < get_local_size(0); i++) {
            atomic_add(output, loc[i]);
        }
    }
}
