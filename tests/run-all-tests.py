# run all the tests before commits
# AMN: from /tests/ % python3 run-all-tests.py
# - This looks really cool, but we're definitely not in the simulator
#       https://ep2016.europython.eu/media/conference/slides/writing-unit-tests-for-c-code-in-python.html 
import subprocess

# track total failures
global testsfailed 
testsfailed = 0
# strings to reuse
doublefree = "dfree"
PVI = "pvi"
passmsg = "\t\ttest passed"
failmsg = "\t\ttest FAILED!"
missinglabelsfail = b'Failstop on policy \n  DoubleFree::FreeT detects free of unallocated memory:  Unallocated, Unallocated, Unallocated, Unallocated\n'
# use for the contains approach.
nofault_cleanexit = b'program terminated (exit code = 0)'

# shell=True did not do what we hoped here. 
def runACFileWithoutInput (filename, policy, expectedoutput):
    print(f"\ttesting {filename} with {policy} policy")
    # run is a blocking call
    completed_run = subprocess.run(["bash", "-c", f"../ccomp -interp -p {policy} {filename}"],
                                   capture_output=True )

    # this is not fancy, but it should keep me from checking in dumb mistakes
    if (expectedoutput in completed_run.stdout):
        print(f"{passmsg}")
    else:
        print(f"{failmsg}\n\t\tret code:{completed_run.returncode}\n\t\toutput:\n\t\t{completed_run.stdout}")
        global testsfailed
        testsfailed+=1

def runACFileWithInput (filename, policy, testinput, expectedoutput):
    print(f"\ttesting {filename} with {policy} policy on input {testinput}")
    with subprocess.Popen(["bash", "-c", f"../ccomp -interp -p {policy} {filename}"],
                          stdout=subprocess.PIPE,
                          stdin=subprocess.PIPE,) as process:
        # no garbage in buffer
        process.stdin.flush()
        # i still love this feature (in py or go)
        stdout, stderr = process.communicate(
            input=f"{testinput}\n".encode("utf-8"), timeout=10
        )
        #print(stdout.decode("utf-8"))
        if ( expectedoutput in stdout):
            print(passmsg)
        else:
            #print(stderr) always None
            print(f"{failmsg}\n\t\tret code:{process.returncode}\n\t\toutput:\n\t\t{stdout}")
            global testsfailed
            testsfailed+=1

if __name__ == '__main__':

    print("beginning /tests/\n=======")
    print("\n=======\npvi tests (without input)\n=======")

    runACFileWithoutInput("printf_test.c", PVI,
                          b'Hello World!\n'
                          )
    runACFileWithoutInput("heap_load_store_ib.c", PVI,
                          nofault_cleanexit)

    runACFileWithoutInput("stack_load_store_ib.c", PVI,
                          nofault_cleanexit)

    runACFileWithoutInput("stack_load_store_ob.c", PVI,
                          b'PVI::StoreT')


    print("\n=======\ndfree tests without input\n=======")
    runACFileWithoutInput("double_free_no_input_handlabelled.c", doublefree,
                          b'DoubleFree::FreeT detects two colors:  FreeColor label1, Unallocated, FreeColor label1, FreeColor label0\n'
                          )

    runACFileWithoutInput("printf_test.c", doublefree,
                          b'Hello World!\n'
                          )
    
    print("=======\ndfree tests with input\n=======")
    # these have much messier outputs from extern calls
    #   don't use an exact output match
    #   If there is a violation, in the array
    #       0th - 2nd free (current)
    #       3rd in array is 1st free (from the header we just tried to free)
    runACFileWithInput("test_fgets_basic.c", doublefree, 
                       "AAAA", b"Hope it doesn't have a problem!")

    runACFileWithInput("rw.c", doublefree,
                       "f", b'1 f')
    
    runACFileWithInput("double_free_basic_input_handlabelled.c",
                       doublefree, "ABCD",
                       b'DoubleFree::FreeT detects two colors:  FreeColor label1, Unallocated, FreeColor label1, FreeColor label0')
    
    # should failstop
    runACFileWithInput("double_free_confused_cleanup_1_handlabelled.c",
                       doublefree, "PP",
                       b'DoubleFree::FreeT detects two colors:  FreeColor label1, Unallocated, FreeColor label1, FreeColor label0')

    # should not
    runACFileWithInput("double_free_confused_cleanup_1_handlabelled.c",
                       doublefree, "AA",
                       nofault_cleanexit)
    # should failstop
    runACFileWithInput("double_free_confused_cleanup_2_handlabelled.c",
                       doublefree, "BBB",
                       b'DoubleFree::FreeT detects two colors: ')
    
    # should not
    runACFileWithInput("double_free_confused_cleanup_2_handlabelled.c",
                       doublefree, "AAA",
                       nofault_cleanexit)
    # TODO this set is more complicated. We need to detect the right double free
    # dfree on x, but not input
    # xx0 skips x's double free, x2x skips input's double free
    runACFileWithInput("double_free_confused_cleanup_multi_handlabelled.c",
                       doublefree, "220",
                       nofault_cleanexit)
    
    runACFileWithInput("double_free_confused_cleanup_multi_handlabelled.c",
                       doublefree, "222",
                       b"DoubleFree::FreeT detects two colors:  FreeColor label4, Unallocated, FreeColor label4, FreeColor label3")

    runACFileWithInput("double_free_confused_cleanup_multi_handlabelled.c",
                       doublefree, "BBB",
                       b'DoubleFree::FreeT detects two colors:  FreeColor label2, Unallocated, FreeColor label2, FreeColor label0')

    # these two seem to be teh same, but if we skipped input's dfree, we should see different behavior for x in these two
    runACFileWithInput("double_free_confused_cleanup_multi_handlabelled.c",
                       doublefree, "!!!",
                       b'DoubleFree::FreeT detects two colors:  FreeColor label2, Unallocated, FreeColor label2, FreeColor label1')

    runACFileWithInput("double_free_confused_cleanup_multi_handlabelled.c",
                       doublefree, "!!0",
                       b'DoubleFree::FreeT detects two colors:  FreeColor label2, Unallocated, FreeColor label2, FreeColor label1')
    
    print("=======\nTests expected to get incorrect output but we'd like to know if that changes unexpectedly\n=======")
    # note tests like this should change when we get the automatic location info
    runACFileWithoutInput("double_free_no_input.c", doublefree,
                          missinglabelsfail)
    
    runACFileWithInput("double_free_basic_input.c",
                       doublefree, "ABCD",
                       missinglabelsfail)
    
    runACFileWithInput("double_free_confused_cleanup_1.c",
                       doublefree, "PP",
                       missinglabelsfail)

    runACFileWithInput("double_free_confused_cleanup_2.c",
                       doublefree, "BBB",
                       missinglabelsfail)
    # TODO should all the confused_clean_up multi be included?

    # end
    print(f"\n=======\ntest suit ending. total tests failed: {testsfailed}")
