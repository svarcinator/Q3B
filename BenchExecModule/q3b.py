import benchexec.tools.template
import benchexec.result as result


class Tool(benchexec.tools.template.BaseTool2):
 

    def name(self):
        """
        Return the name of the tool, formatted for humans.
        """
        return "q3b"
    
    def program_files(self, executable):
        paths = self.REQUIRED_PATHS
        return [executable] + self._program_files_from_executable(
            executable, paths, parent_dir=True
        )
    
    def executable(self, tool_locator):
        """
        Find the path to the executable file that will get executed.
        This method always needs to be overridden,
        and most implementations will look similar to this one.
        The path returned should be relative to the current directory.
        """
        
        executable = tool_locator.find_executable("q3b")
        self._version = self.version(executable)
        #print(f"Found executable {executable}")
        
        return executable
    
    def determine_result(self, run):
        # "cmdline", "exit_code", "output", "termination_reason"
    
        if run.was_timeout:
            return result.RESULT_TIMEOUT
        
        for line in run.output:
            if line.startswith('sat'):
                return result.RESULT_TRUE_PROP
            elif line.startswith('unsat'):
                return result.RESULT_FALSE_PROP
        if run.exit_code.signal == 9:
            status = "KILLED BY SIGNAL 9"
        elif run.exit_code.signal == 6:
            status = "ABORTED"
        elif run.exit_code.signal == 15:
            status = "KILLED"
        elif run.exit_code.signal == 11:
            status = "SEGFAULT"
        else:
            status = f"ERROR ({run.exit_code.value}, termination reason={run.termination_reason}, output={run.output}, exit signal {run.exit_code.signal})"

        
        return status
    
    def version(self, executable):
       return self._version_from_tool(executable)
