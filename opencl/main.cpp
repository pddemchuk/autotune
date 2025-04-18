#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>
#include <CL/cl.h>

#define MAXSIZE (32)


int main(int argc, const char *argv[]) {
    FILE *csv_file;

    int *array = (int *)malloc(MAXSIZE * sizeof(int));
    printf("--- Before ---\n");
    for (int i = 0; i < MAXSIZE; i++) {
        array[i] = MAXSIZE - i;
        printf("array[%d]: %d\n", i, array[i]);
    }

    cl_platform_id platform;
    cl_device_id device;
    cl_context context;
    cl_program program;
    cl_kernel kernel;
    cl_command_queue queue;
    FILE *programHandle;
    char *programBuffer;
    size_t programSize;
    clGetPlatformIDs(1, &platform, NULL);
    clGetDeviceIDs(platform, CL_DEVICE_TYPE_GPU, 1, &device, NULL);
    cl_uint units;
    clGetDeviceInfo(device, CL_DEVICE_MAX_COMPUTE_UNITS, sizeof(units), &units, NULL);
    int sum = 0;
    context = clCreateContext(NULL, 1, &device, NULL, NULL, NULL);
    programHandle = fopen("kernel.cl", "r");

    fseek(programHandle, 0, SEEK_END);
    programSize = ftell(programHandle);
    rewind(programHandle);
    programBuffer = (char *)malloc(programSize + 1);
    memset(programBuffer, 0, programSize + 1);
    fread(programBuffer, sizeof(char), programSize, programHandle);
    fclose(programHandle);
    program = clCreateProgramWithSource(context, 1, (const char **)&programBuffer, &programSize, NULL);
    free(programBuffer);
    int err = clBuildProgram(program, 1, &device, NULL, NULL, NULL);

    if (err != CL_SUCCESS) {
        printf("clBuildProgram: %d\n", err);
        char log[0x10000];
        clGetProgramBuildInfo(program, device, CL_PROGRAM_BUILD_LOG, 0x10000, log, NULL);
        printf("\n%s\n", log);
        return (EXIT_FAILURE);
    }

	err = 0;
    kernel = clCreateKernel(program, "sum_even", &err);

    queue = clCreateCommandQueue(context, device, 0, NULL);
    cl_mem my_cl_array = clCreateBuffer(context, CL_MEM_READ_WRITE, MAXSIZE * sizeof(int), NULL, NULL);
    clEnqueueWriteBuffer(queue, my_cl_array, CL_TRUE, 0, MAXSIZE * sizeof(int), array, 0, NULL, NULL);
    cl_mem my_cl_sum = clCreateBuffer(context, CL_MEM_READ_WRITE, sizeof(int), NULL, NULL);
    clEnqueueWriteBuffer(queue, my_cl_sum, CL_TRUE, 0, sizeof(int), &sum, 0, NULL, NULL);

    double mid_gb = 0;
    double mid_time = 0;

    int C = 100; //count of re-runs

    printf("\ngo\n");

    int SM = 1;
    int TS_real = 4;
    int WG_real = 1;

    mid_time = 0;
    mid_gb= 0;

    for (int t = 0; t < C; t++) {

		size_t global_item_size = SM * WG_real;
        size_t local_item_size = WG_real;

        clSetKernelArg(kernel, 0, sizeof(cl_mem), &my_cl_array);
        clSetKernelArg(kernel, 1, sizeof(cl_mem), &my_cl_sum);
        clSetKernelArg(kernel, 2, sizeof(cl_uint) *local_item_size, NULL);
        clSetKernelArg(kernel, 3, sizeof(cl_uint), &TS_real);

        struct timeval initial_time, final_time;
        gettimeofday(&initial_time, NULL);

        clEnqueueNDRangeKernel(queue, kernel, 1, NULL, &global_item_size, &local_item_size, 0, NULL, NULL);

        clEnqueueReadBuffer(queue, my_cl_sum, CL_TRUE, 0, sizeof(int), &sum, 0, NULL, NULL);

        gettimeofday(&final_time, NULL);

        long long exec_time = ((long long)final_time.tv_sec * 1000000 + final_time.tv_usec) -
        		((long long)initial_time.tv_sec * 1000000 + initial_time.tv_usec);

        //printf("\nExecution time was %llu microseconds\n", exec_time);

        float bandwidth = 1e-9*(float)(MAXSIZE*sizeof(cl_uint)) / ((float)exec_time/1e6);

        //printf("Memory bandwidth %.2f GB/sec\n", bandwidth);

        mid_time += exec_time;
        mid_gb += bandwidth;

        //printf("--- After ---\n");
        //printf("sum: %d\n", sum);

        //clEnqueueReadBuffer(queue, my_cl_array, CL_TRUE, 0, MAXSIZE * sizeof(int), array, 0, NULL, NULL);

        clFlush(queue);
    }

    printf("\nSM = %d; WG = %d; TS = %d; time = %lf; gb = %lf \n\n",SM, WG_real, TS_real, mid_time / (C*1000), mid_gb / C);

    clFinish(queue);
    clReleaseKernel(kernel);
    clReleaseProgram(program);
    clReleaseMemObject(my_cl_array);
    clReleaseMemObject(my_cl_sum);
    clReleaseCommandQueue(queue);
    clReleaseContext(context);
    return 0;
}
