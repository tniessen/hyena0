#include "solver.h"

#include <cassert>
#include <sstream>

#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

s_expr_list solve(const s_expr_list& stmts, bool ef_mode) {
  using std::literals::string_literals::operator""s;
  std::string file = "yices";
  std::vector<char*> argv({file.data(), ef_mode ? "--mode=ef"s.data() : "--mode=one-shot"s.data(), nullptr});

  int stdin_fds[2];
  assert(pipe(stdin_fds) == 0);

  int stdout_fds[2];
  assert(pipe(stdout_fds) == 0);

  pid_t child_pid = fork();
  if (child_pid == 0) {
    dup2(stdin_fds[0], 0);
    close(stdin_fds[1]);
    close(stdout_fds[0]);
    dup2(stdout_fds[1], 1);
    close(stdout_fds[1]);
    execvp(file.c_str(), argv.data());
    perror(("\nFailed to execute '" + file + "'").c_str());
    abort();
  }

  assert(child_pid > 0);

  close(stdin_fds[0]);
  close(stdout_fds[1]);

  std::stringstream ss;
  for (const auto& stmt : stmts) {
    ss << stmt << std::endl;
  }
  const std::string smt_input = std::move(ss).str();

  FILE* child_stdin = fdopen(stdin_fds[1], "wb");
  fwrite(smt_input.data(), 1, smt_input.size(), child_stdin);
  fclose(child_stdin);

  FILE* child_stdout = fdopen(stdout_fds[0], "rb");
  assert(child_stdout != nullptr);
  std::string buffer;
  buffer.resize(64 * 1024);
  size_t stdout_size = fread(buffer.data(), 1, buffer.size(), child_stdout);
  assert(!ferror(child_stdout));
  assert(feof(child_stdout));
  fclose(child_stdout);
  assert(stdout_size < buffer.size());
  buffer.resize(stdout_size);
  int child_status;
  waitpid(child_pid, &child_status, 0);
  assert(WIFEXITED(child_status));
  assert(WEXITSTATUS(child_status) == 0);

  return *s_expr::parse_multiple(buffer);
}
