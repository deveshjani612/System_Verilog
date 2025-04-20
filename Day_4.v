| #    | Section           | Description                                      | Link                                     | Type        | Weight |
|------|-------------------|--------------------------------------------------|------------------------------------------|-------------|--------|
| 1    | Simulation         |                                                  |                                          |             |        |
| 1.1  | Protocol Checks    | Verify reset & clock domain crossing behavior   | assert_reset_sync, assert_clk_stable     | Assertion   | 1      |
| 1.2  | Transaction Coverage | Cover transactions through main path          | main_path_cg                             | CoverGroup  | 1      |
| 1.3  | Edge Cases         | Cover corner-case values and transitions        | corner_cases_cross                       | Cross       | 1      |
| 2    | Bus Access         |                                                  |                                          |             |        |
| 2.1  | Read/Write Access  | Cover reads & writes across valid addresses     | addr_rw_cover                            | Coverpoint  | 1      |
| 2.2  | Illegal Access     | Assert invalid address access detection         | assert_illegal_access                    | Assertion   | 1      |
| 3    | Random Testing     |                                                  |                                          |             |        |
| 3.1  | Base Test          | Basic functionality and reset                   | test_base                                | Test        | 1      |
| 3.2  | Random Stimulus    | Run randomized test scenarios                   | test_random_*                            | Test        | 1      |
| 4    | Coverage Metrics   |                                                  |                                          |             |        |
| 4.1  | Code Coverage      | 100% line, branch, and toggle coverage          | hdl/system_block                         | Instance    | 1      |
