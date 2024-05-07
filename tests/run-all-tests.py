# run all the tests before commits
# AMN: from /tests/ % python3 run-all-tests.py
# - This looks really cool, but we're definitely not in the simulator
#       https://ep2016.europython.eu/media/conference/slides/writing-unit-tests-for-c-code-in-python.html 
import subprocess

# track total failures
global testsfailed 
global testspassed
global testsrun
testsfailed = 0
testsrun = 0
testspassed = 0
defaulttimeout = 3000 # default # of steps to allow to run
    # getchar eatsa lot of steps 
# strings to reuse
doublefree = "dfree"
PVI = "pvi"
dfreeXpvi = "dfxpvi"
heapproblem = "heapproblem"
passmsg = "\t\ttest passed"
failmsg = "\t\ttest FAILED!"
# after adding locations, these no longer have the same error
#missinglabelsfail = b'Failstop on policy \n  DoubleFree::FreeT detects free of unallocated memory:  Unallocated, Unallocated, Unallocated, Unallocated\n'
# use for the contains approach.
nofault_cleanexit = b'program terminated (exit code = 0)'

# shell=True did not do what we hoped here. 
def runACFileWithoutInput (filename, policy, expectedoutput):
    print(f"\ttesting {filename} with {policy} policy")
    # run is a blocking call
    completed_run = subprocess.run(["bash", "-c", f"../ccomp -interp -timeout {defaulttimeout} -p {policy} {filename}"],
                                   capture_output=True )

    global testsrun
    testsrun+=1

    # this is not fancy, but it should keep me from checking in dumb mistakes
    if (expectedoutput in completed_run.stdout or expectedoutput in completed_run.stderr):
        #print(f"{passmsg}")
        global testspassed
        testspassed +=1
    else:
        print(f"{failmsg}\n\t\tret code:{completed_run.returncode}\n\t\tstdoutput:\n\t\t{completed_run.stdout}\n\t\tstderr:\n{completed_run.stderr}\n\t\texpected:\n\t\t{expectedoutput}\n")
        global testsfailed
        testsfailed+=1

def runACFileWithInput (filename, policy, testinput, expectedoutput):
    print(f"\ttesting {filename} with {policy} policy on input {testinput}")
    with subprocess.Popen(["bash", "-c", f"../ccomp -interp -timeout {defaulttimeout} -p {policy} {filename}"],
                          stdout=subprocess.PIPE,
                          stdin=subprocess.PIPE,
                          stderr=subprocess.PIPE) as process:
        # no garbage in buffer
        process.stdin.flush()
        # i still love this feature (in py or go)
        stdout, stderr = process.communicate(
            input=f"{testinput}\n".encode("utf-8"), timeout=10
        )
    
        global testsrun
        testsrun+=1

        #print(stdout.decode("utf-8"))
        if ( expectedoutput in stdout or expectedoutput in stderr):
            #print(passmsg)
            global testspassed
            testspassed +=1
        else:
            print(f"{failmsg}\n\t\tret code:{process.returncode}\n\t\toutput:\n\t\t{stdout}\n\t\tstderr:\n\t\t{stderr}\n\t\texpected:\n\t\t{expectedoutput}\n")
            global testsfailed
            testsfailed+=1

# these tests should always pass, regardless of policy: IO, infra 
def runSanityTests (policy):
    runACFileWithoutInput("printf_test.c", policy,
                          b'Hello World!\n')
    runACFileWithInput("rw.c", policy, "f", b'1 f')

    # there is a slight testing artifact here. You don't see the \0
    #     when you run the test manually, but the test harness does see it
    runACFileWithInput("test_getchar_basic.c", policy, "Hello",
                          b'You entered H\x00. Hope it doesn\'t have a problem!')   
    runACFileWithInput("test_getchar_loop.c", policy, "Hello", 
                          b'You entered: Hello')

def runConcreteAllocChecks(policy):
    runACFileWithoutInput("allocator_smallestpossible.c", policy,
                          nofault_cleanexit)
    runACFileWithoutInput("allocator_single.c", policy,
                          nofault_cleanexit)
    runACFileWithoutInput("allocator_basic.c", policy,
                          nofault_cleanexit)
    runACFileWithoutInput("allocator_single_OOM.c", policy,
                          nofault_cleanexit)

if __name__ == '__main__':

    print("\n=======\nSanity Tests, Infrastructure (IO, Alloc) Tests\n=======")
    # run on every policy supported 
    # poked SNA. I dont think PVI is supposed to blow up here
    #runSanityTests(PVI)
    runSanityTests(doublefree)
    runSanityTests(heapproblem)
    # restore once PVI is fixed/sorted
    #runSanityTests(dfreeXpvi)

    # test the concrete allocator on policies that use it
    runConcreteAllocChecks(doublefree)
    runConcreteAllocChecks(heapproblem)
    runConcreteAllocChecks(dfreeXpvi) # a slight lie. PVI is meant for FLAlloc

    # So far theres only one that uses FLAlloc
    runACFileWithoutInput("allocator_smallestpossible.c", PVI,
                          nofault_cleanexit)
    runACFileWithoutInput("allocator_single.c", PVI,
                          nofault_cleanexit)
    runACFileWithoutInput("allocator_basic.c", PVI,
                          nofault_cleanexit)
    runACFileWithoutInput("allocator_single_OOM.c", PVI,
                          nofault_cleanexit)

    print("\n=======\nMultipolicy (Product.v) without input\n=======")
    # fail  left
    runACFileWithoutInput("double_free_no_input.c", dfreeXpvi,
                          b'ProdLeft||DoubleFree||FreeT detects two frees| source location double_free_no_input.c:8, location double_free_no_input.c:9\n'
                          )
    #fail right
    runACFileWithoutInput("stack_load_store_ob.c", dfreeXpvi,
                          b'ProdRight||PVI || StoreT tag_eq_dec Failure at stack_load_store_ob.c:8')

    # pass both
    runACFileWithoutInput("heap_load_store_ib.c", dfreeXpvi,
                          nofault_cleanexit)

    print("\n=======\n Policy Specific\n=======")
    print("\n=======\npvi tests\n=======")

    runACFileWithoutInput("printf_test.c", PVI,
                          b'Hello World!\n'
                          )
    runACFileWithoutInput("heap_load_store_ib.c", PVI,
                          nofault_cleanexit)

    runACFileWithoutInput("stack_load_store_ib.c", PVI,
                          nofault_cleanexit)

    runACFileWithoutInput("stack_load_store_ob.c", PVI,
                          b'PVI || StoreT')

    
    print("=======\ndfree tests \n=======")
    
    runACFileWithoutInput("double_free_no_input.c", doublefree,
                          b'DoubleFree||FreeT detects two frees| source location double_free_no_input.c:8, location double_free_no_input.c:9\n'
                          )
    # these have much messier outputs from extern calls
    #   don't use an exact output match
    #   If there is a violation, in the array
    #       0th - 2nd free (current)
    #       3rd in array is 1st free (from the header we just tried to free)
    runACFileWithInput("test_fgets_basic.c", doublefree, 
                       "AAAA", b"Hope it doesn't have a problem!")
    
    runACFileWithInput("double_free_basic_input.c",
                       doublefree, "ABCD",
                       b'DoubleFree||FreeT detects two frees| source location double_free_basic_input.c:14, location double_free_basic_input.c:15')

    # should failstop
    runACFileWithInput("double_free_confused_cleanup_1.c",
                       doublefree, "PP",
                       b'DoubleFree||FreeT detects two frees| source location double_free_confused_cleanup_1.c:18, location double_free_confused_cleanup_1.c:20')

    # should not
    runACFileWithInput("double_free_confused_cleanup_1.c",
                       doublefree, "AA",
                       nofault_cleanexit)
    # should failstop
    runACFileWithInput("double_free_confused_cleanup_2.c",
                       doublefree, "BBB",
                       b'DoubleFree||FreeT detects two frees| source location double_free_confused_cleanup_2.c:39, location double_free_confused_cleanup_2.c:47')

    # should failstop with a different dfree
    runACFileWithInput("double_free_confused_cleanup_2.c",
                       doublefree, "!!!",
                       b'DoubleFree||FreeT detects two frees| source location double_free_confused_cleanup_2.c:41, location double_free_confused_cleanup_2.c:47')
    
    # should not
    runACFileWithInput("double_free_confused_cleanup_2.c",
                       doublefree, "AAA",
                       nofault_cleanexit)
    # This set is more complicated. We need to detect the right double free
    # dfree on x, but not input
    # xx0 skips x's double free, x2x skips input's double free
    runACFileWithInput("double_free_confused_cleanup_multi.c",
                       doublefree, "220",
                       nofault_cleanexit)
    
    runACFileWithInput("double_free_confused_cleanup_multi.c",
                       doublefree, "222",
                       b"DoubleFree||FreeT detects two frees| source location double_free_confused_cleanup_multi.c:77, location double_free_confused_cleanup_multi.c:79")

    runACFileWithInput("double_free_confused_cleanup_multi.c",
                       doublefree, "BBB",
                       b'DoubleFree||FreeT detects two frees| source location double_free_confused_cleanup_multi.c:63, location double_free_confused_cleanup_multi.c:71')

    # these two seem to be teh same, but if we somehow missed input's dfree, we would see different behavior for x in these two
    runACFileWithInput("double_free_confused_cleanup_multi.c",
                       doublefree, "!!!",
                       b'DoubleFree||FreeT detects two frees| source location double_free_confused_cleanup_multi.c:65, location double_free_confused_cleanup_multi.c:71')

    runACFileWithInput("double_free_confused_cleanup_multi.c",
                       doublefree, "!!0",
                       b'DoubleFree||FreeT detects two frees| source location double_free_confused_cleanup_multi.c:65, location double_free_confused_cleanup_multi.c:71')

    runACFileWithInput("double_free_basic_nonsensefree.c",
                       doublefree, "hi",
                       # old version 
                       #b"DoubleFree||FreeT detects free of unallocated memory| source location double_free_basic_nonsensefree.c:18" )
                       # version where the parseheader happens before freeT does 
                       #b"ConcreteAllocator| parse_header | Header is undefined")
                       b"DoubleFree||FreeT detects corrupted alloc header| source location double_free_basic_nonsensefree.c:18")
    
    print("=======\nHeap Problems Tests\n=======")
    # heaproblem not responsible for making sure you dont OOM your heap. 
    #      users still need to check for 0 :p 
    runACFileWithoutInput("heapproblem_overread_basic_nopad.c", heapproblem,
                          b"HeapProblem|| Heap Overread| LoadT tried to read unallocated heap memory at  src location heapproblem_overread_basic_nopad.c:32")    
    runACFileWithoutInput("heapproblem_overread_basic_pad.c", heapproblem,
                          b"HeapProblem|| Heap Overread| LoadT read past the end into padding belonging to  heapproblem_overread_basic_pad.c:36 at heapproblem_overread_basic_pad.c:46")    
    runACFileWithInput("heapproblem_overread_getchar_3_faults.c",
                       heapproblem, "hellohihowareyou",
                       nofault_cleanexit)
    runACFileWithInput("heapproblem_overread_getchar_3_faults.c",
                       heapproblem, "000E0000000",
                       nofault_cleanexit)
    runACFileWithInput("heapproblem_overread_getchar_3_faults.c",
                       heapproblem, "P0000000000",
                       b'HeapProblem|| Heap Overread| LoadT read past the end into padding belonging to  heapproblem_overread_getchar_3_faults.c:73 at heapproblem_overread_getchar_3_faults.c:92')
    runACFileWithInput("heapproblem_overread_getchar_3_faults.c",
                       heapproblem, "0I000000000",
                       b'HeapProblem|| Heap Overread| LoadT read past the end into padding belonging to  heapproblem_overread_getchar_3_faults.c:73 at heapproblem_overread_getchar_3_faults.c:107')
    runACFileWithInput("heapproblem_overread_getchar_3_faults.c",
                       heapproblem, "00P00000000",
                       b'HeapProblem|| Heap Overread| LoadT tried to read allocator header belonging to  heapproblem_overread_getchar_3_faults.c:73 at heapproblem_overread_getchar_3_faults.c:118')
    
    
    # end
    print(f"\n=======\ntest suit ending.\n\ttotal tests run: {testsrun}\n\ttotal failed: {testsfailed}\n\ttotal passed: {testspassed}")
