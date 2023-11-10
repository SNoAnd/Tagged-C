# run all the tests before commits
# AMN: from /tests/ % python3 run-all-tests.py
# - This looks really cool, but we're definitely not in the simulator
#       https://ep2016.europython.eu/media/conference/slides/writing-unit-tests-for-c-code-in-python.html 
import subprocess

global testsfailed 
testsfailed = 0
passmsg = "\t\ttest passed"
failmsg = "\t\ttest FAILED!"
missinglabelsfail = b'Failstop on policy \n  DoubleFree::FreeT detects free of unallocated memory:  Unallocated, Unallocated, Unallocated, Unallocated\n'
# use for the contains approach.
nofault_cleanexit = b'program terminated (exit code = 0)'

# shell=True did not do what we hoped here. 
# failstop found in output.stdout
# TODO maybe use the in check for these tests as well
def runACFileWithoutInput (filename, policy, expectedoutput):
    print(f"\ttesting {filename} with {policy} policy")
    # run is a blocking call
    completed_run = subprocess.run(["bash", "-c", f"../ccomp -interp -p {policy} {filename}"],
                                   capture_output=True )
    #unexpectedly to me at least, the interpreter exit 0's for a failstop msg                          
    #print(f"exit code was {completed_run.returncode}")
    #print(completed_run.stdout)

    # this is not fancy, but it should keep me from checking in dumb mistakes
    if (completed_run.stdout == expectedoutput):
        print(passmsg)
    else:
        print(failmsg)
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
            print(failmsg)
            global testsfailed
            testsfailed+=1
# tests still missing in /tests/
#   - confused clean up multi is missing 
#   - heap_load_store_ib.c policy? 
#   - stack_load_store_ib.c
#   - stack_load_store_ob.c
if __name__ == '__main__':

    doublefree = "dfree"
    print("beginning /tests/\n=======\ntests without input\n=======")
    runACFileWithoutInput("double_free_no_input_handlabelled.c", doublefree,
                          b'Failstop on policy \n  DoubleFree::FreeT detects two colors:  FreeColor label1, Unallocated, FreeColor label1, FreeColor label0\n'
                          )

    runACFileWithoutInput("printf_test.c", doublefree,
                          b'Hello World!\nTime 160: observable event: extcall printf(2986LL) -> 13\nTime 166: program terminated (exit code = 0)\n'
                          )
    
    runACFileWithoutInput("printf_test.c", "pvi",
                          b'Hello World!\nTime 160: observable event: extcall printf(2986LL) -> 13\nTime 166: program terminated (exit code = 0)\n'
                          )
    
    print("=======\ntests with input\n=======")
    # these have much messier outputs from extern calls
    #   don't use an exact output match
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
    # end
    print(f"\n=======\ntest suit ending. total tests failed: {testsfailed}")