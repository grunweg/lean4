// Lean compiler output
// Module: Lean.Server.FileWorker
// Imports: Init Init.System.IO Std.Data.RBMap Lean.Environment Lean.Data.Lsp Lean.Data.Json.FromToJson Lean.Util.Paths Lean.Server.Utils Lean.Server.Snapshots Lean.Server.AsyncList Lean.Server.FileWorker.Utils Lean.Server.FileWorker.RequestHandling Lean.Server.FileWorker.WidgetRequests Lean.Server.Rpc.Basic Lean.Widget.InteractiveDiagnostic
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__40;
lean_object* l_IO_setRandSeed(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__8;
lean_object* l_Lean_Server_FileWorker_RpcSession_keptAlive(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_CancelToken_check___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_insert___at_Lean_Server_FileWorker_handleRpcConnect___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__9;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapMAux___at_Lean_Server_FileWorker_compileHeader___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspResponseError___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_get_stdout(lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__45;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__2;
static lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__4;
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__2(lean_object*, lean_object*);
extern lean_object* l_String_instInhabitedString;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__39;
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
static lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__3;
lean_object* l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_fromJsonDidOpenTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_114_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcRelease___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__57;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__9;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_erase___at_Lean_Server_FileWorker_handleCancelRequest___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Parser_parseHeader(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__36;
lean_object* l_String_split___at_Lean_stringToMessageData___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcConnectParams____x40_Lean_Data_Lsp_Extra___hyg_1068_(lean_object*);
static lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__5;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__3;
lean_object* l_Lean_Option_get___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_245____spec__1(lean_object*, lean_object*);
lean_object* lean_environment_set_main_module(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__4;
lean_object* l_String_firstDiffPos(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__1___closed__1;
lean_object* l_Lean_JsonNumber_toString(lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__35;
uint8_t lean_uint32_to_uint8(uint32_t);
static lean_object* l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__3;
static lean_object* l_Lean_Server_FileWorker_handleNotification___closed__1;
lean_object* l_Lean_Server_publishProgressDone(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__5;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_DocumentUri_toPath_x3f(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_CancelToken_check___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_del___at_Lean_Server_FileWorker_mainLoop___spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcRelease(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcConnect(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__2;
lean_object* l_IO_FS_Stream_readLspMessage(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_CancelToken_check___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___spec__1___closed__1;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__1;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__44;
lean_object* l_Lean_Elab_headerToImports(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Server_publishProgressAtPos(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__2;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__60;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__47;
static lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__5;
lean_object* l_Std_RBNode_find___at_Lean_Server_registerRpcCallHandler___spec__1(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcConnect___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__7;
lean_object* l_IO_throwServerError___rarg(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__19;
lean_object* l_Array_toPersistentArray___rarg(lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__27;
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Server_FileWorker_handleNotification___closed__4;
LEAN_EXPORT lean_object* l_Std_RBNode_insert___at_Lean_Server_FileWorker_handleRpcConnect___spec__1(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_unfoldCmdSnaps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_FileWorker_CancelToken_new(lean_object*);
lean_object* l_IO_FS_Stream_readMessage(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_processHeader(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_erase___at_Lean_Server_FileWorker_mainLoop___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_parseParams___rarg___closed__1;
static lean_object* l_Lean_Server_FileWorker_initAndRunWorker___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcConnect___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__6;
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__6(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___closed__1;
static lean_object* l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__3___closed__1;
extern lean_object* l_Lean_maxRecDepth;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_queueRequest___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleNotification___closed__2;
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapM___at_Lean_Server_FileWorker_compileHeader___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleNotification___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__26;
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapM___at_Lean_Server_FileWorker_compileHeader___spec__6(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___closed__2;
lean_object* l_Std_RBNode_setBlack___rarg(lean_object*);
lean_object* l_IO_appDir(lean_object*);
lean_object* l_Lean_Widget_msgToInteractiveDiagnostic(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__2;
static lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_mainLoop___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCancelRequest___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableNot___rarg(uint8_t);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__17;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRequest___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__9;
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Task_Priority_dedicated;
static lean_object* l_Lean_Server_FileWorker_initAndRunWorker___closed__5;
lean_object* l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleNotification(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleNotification___closed__3;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__43;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__2;
lean_object* l_Lean_Server_Snapshots_reparseHeader(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_FileWorker_mainLoop___spec__4___at_Lean_Server_FileWorker_mainLoop___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__1(size_t, size_t, lean_object*);
static lean_object* l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__3;
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2(lean_object*, uint64_t, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__5;
lean_object* l_IO_AsyncList_append___rarg(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__15;
static lean_object* l_Lean_Server_FileWorker_compileHeader___closed__4;
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_FileWorker_mainLoop___spec__4___at_Lean_Server_FileWorker_mainLoop___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_putStrLn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_insert___at_Lean_Server_FileWorker_queueRequest___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleDidChange___closed__5;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleRequest___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__28;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__14;
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_appendTrees___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkState(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcKeepAliveParams____x40_Lean_Data_Lsp_Extra___hyg_1585_(lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3;
static lean_object* l_Lean_Server_FileWorker_initAndRunWorker___closed__1;
lean_object* l_Std_RBNode_balRight___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_unfoldCmdSnaps___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_RBNode_isBlack___rarg(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_unfoldAsync___at_Lean_Server_FileWorker_unfoldCmdSnaps___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcKeepAlive___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcReleaseParams____x40_Lean_Data_Lsp_Extra___hyg_1446_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initAndRunWorker___boxed__const__1;
static lean_object* l_Lean_Server_FileWorker_handleNotification___closed__5;
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Server_handleLspRequest(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspResponseError(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspMessage(lean_object*, lean_object*, lean_object*);
static uint8_t l_Lean_Server_FileWorker_handleDidChange___closed__3;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
lean_object* lean_io_prim_handle_get_line(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__61;
static lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__6;
static lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__3___closed__1;
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_queueRequest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcKeepAlive(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__12;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRequest___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRequest(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___closed__6;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleDidChange___closed__1;
static uint8_t l_Lean_Server_FileWorker_handleDidChange___closed__2;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__59;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__31;
lean_object* l_Lean_Server_RequestError_toLspResponseError(lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
static lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__7;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_118_(lean_object*, lean_object*);
lean_object* lean_module_name_of_file(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_del___at_Lean_Server_FileWorker_mainLoop___spec__3(uint64_t, lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__3;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__24;
lean_object* l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonCancelParams____x40_Lean_Data_Lsp_Basic___hyg_109_(lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__63;
lean_object* l_List_takeWhile___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_initAndRunWorker___closed__6;
lean_object* l_Lean_realPathNormalized(lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__4;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updatePendingRequests___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__58;
lean_object* lean_get_prefix(lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__55;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__53;
lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* lean_io_exit(uint8_t, lean_object*);
extern lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot;
lean_object* l_Std_RBNode_balLeft___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___at_Lean_Server_FileWorker_unfoldCmdSnaps___spec__3___closed__1;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_mainLoop(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Task_Priority_default;
lean_object* lean_io_has_finished(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Server_publishDiagnostics(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__5(lean_object*, lean_object*);
extern lean_object* l_System_FilePath_exeExtension;
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___at_Lean_Server_FileWorker_unfoldCmdSnaps___spec__3___lambda__1(lean_object*);
lean_object* l_IO_AsyncList_ofList___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleRequest___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__42;
lean_object* l_Lean_Server_Snapshots_Snapshot_diagnostics(lean_object*);
lean_object* l_Lean_initSearchPath(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__18;
static lean_object* l_Lean_Server_FileWorker_handleRequest___closed__1;
lean_object* l_Lean_Server_Snapshots_parseNextCmd(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__30;
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__7;
static lean_object* l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initializeWorker(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_FileWorker_handleRequest___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__6;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__37;
lean_object* lean_mk_empty_environment(uint32_t, lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__5;
lean_object* l_IO_AsyncList_updateFinishedPrefix___rarg(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Server_FileWorker_RpcSession_new(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__8;
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__4;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcConnect___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
lean_object* lean_io_getenv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_server_worker_main(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__8;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_queueRequest(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_parseParams___rarg___closed__2;
lean_object* l_IO_AsyncList_finishedPrefix___rarg(lean_object*);
lean_object* l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63_(lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__56;
static lean_object* l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__23;
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_System_FilePath_fileName(lean_object*);
uint8_t l_Std_RBNode_isRed___rarg(lean_object*);
lean_object* l_Std_PersistentArray_toArray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_FileWorker_handleRpcRelease___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_unfoldAsync_step___at_Lean_Server_FileWorker_unfoldCmdSnaps___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_initAndRunWorker___closed__3;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__20;
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__5;
uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_802____at___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_beqDiagnosticWith____x40_Lean_Data_Lsp_Diagnostics___hyg_703____spec__3(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(lean_object*, lean_object*);
lean_object* l_List_get_x21___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__49;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_FileWorker_handleRequest___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_mainLoop___closed__2;
lean_object* l_Lean_Json_mkObj(lean_object*);
uint8_t l_Lean_Server_Snapshots_Snapshot_isAtEnd(lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__32;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__10;
static lean_object* l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__4;
static lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__46;
static lean_object* l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapMAux___at_Lean_Server_FileWorker_compileHeader___spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at_Lean_Server_FileWorker_initAndRunWorker___spec__5(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__6;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__29;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__25;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Server_FileWorker_queueRequest___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___at_Lean_Server_FileWorker_unfoldCmdSnaps___spec__3(lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_erase___at_Lean_Server_FileWorker_mainLoop___spec__2(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_eprint___at_IO_eprintln___spec__1(lean_object*, lean_object*);
lean_object* lean_io_get_random_bytes(size_t, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__34;
lean_object* l_String_trim(lean_object*);
lean_object* l_List_dropLast___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_updateDocument___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Server_foldDocumentChanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_FileWorker_mainLoop___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleDidChange___closed__4;
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_IO_FS_Stream_withPrefix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_SearchPath_parse(lean_object*);
lean_object* l_Lean_Server_FileWorker_RpcSession_release(lean_object*, size_t);
lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog(lean_object*);
static lean_object* l_Lean_Server_FileWorker_initAndRunWorker___closed__4;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_FileWorker_handleRpcRelease___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDidChange(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__4;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__48;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updatePendingRequests(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_getLast_x21___rarg(lean_object*, lean_object*);
lean_object* lean_get_stderr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_unfoldCmdSnaps(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__38;
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__21;
lean_object* l_Lean_Server_FileWorker_CancelToken_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initAndRunWorker(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_CancelToken_check___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___spec__1___closed__2;
static lean_object* l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__8;
lean_object* l_Lean_Server_maybeTee(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___closed__3;
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__7;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__50;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_updateDocument___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
lean_object* lean_get_stdin(lean_object*);
uint8_t l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__1;
lean_object* l_IO_FS_Handle_readToEnd_loop(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_workerMain___closed__1;
lean_object* l_ByteArray_toUInt64LE_x21(lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__11;
lean_object* l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_fromJsonDidChangeTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_422_(lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___closed__5;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_FileWorker_handleRequest___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_workerMain___boxed__const__1;
lean_object* l_EIO_toBaseIO___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonRpcConnected____x40_Lean_Data_Lsp_Extra___hyg_1178_(uint64_t);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__52;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__51;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__10;
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__3(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__62;
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_FileWorker_mainLoop___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__33;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___closed__1;
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCancelRequest(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* l_Lean_Server_FileWorker_RpcSession_hasExpired(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__41;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRequest___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_del___at_Lean_Server_FileWorker_handleCancelRequest___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initAndRunWorker___boxed__const__2;
lean_object* l_IO_ofExcept___at_IO_Process_output___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_compileNextCmd(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_initAndRunWorker___closed__7;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__6;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__22;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__54;
static lean_object* _init_l_Lean_Server_FileWorker_CancelToken_check___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_CancelToken_check___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_CancelToken_check___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_st_ref_get(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = l_Lean_Server_FileWorker_CancelToken_check___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___spec__1___closed__1;
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = l_Lean_Server_FileWorker_CancelToken_check___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___spec__1___closed__1;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_4, 0);
lean_dec(x_14);
x_15 = l_Lean_Server_FileWorker_CancelToken_check___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___spec__1___closed__2;
lean_ctor_set(x_4, 0, x_15);
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec(x_4);
x_17 = l_Lean_Server_FileWorker_CancelToken_check___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___spec__1___closed__2;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = l_Lean_Server_Snapshots_Snapshot_endPos(x_1);
x_9 = 0;
lean_inc(x_3);
lean_inc(x_2);
x_10 = l_Lean_Server_publishProgressAtPos(x_2, x_8, x_3, x_9, x_7);
lean_dec(x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
x_13 = l_Lean_Server_Snapshots_compileNextCmd(x_12, x_1, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Server_FileWorker_CancelToken_check___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___spec__1(x_4, x_6, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_16, 0, x_22);
return x_16;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_25 = x_17;
} else {
 lean_dec_ref(x_17);
 x_25 = lean_box(0);
}
if (lean_is_scalar(x_25)) {
 x_26 = lean_alloc_ctor(0, 1, 0);
} else {
 x_26 = x_25;
}
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_17, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_dec(x_16);
lean_inc(x_14);
x_31 = l_Lean_Server_Snapshots_Snapshot_diagnostics(x_14);
x_32 = l_Std_PersistentArray_toArray___rarg(x_31);
x_33 = l_Lean_Server_publishDiagnostics(x_2, x_32, x_3, x_30);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_33, 0, x_17);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
lean_ctor_set(x_17, 0, x_14);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_17);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_free_object(x_17);
lean_dec(x_14);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_17);
x_42 = lean_ctor_get(x_16, 1);
lean_inc(x_42);
lean_dec(x_16);
lean_inc(x_14);
x_43 = l_Lean_Server_Snapshots_Snapshot_diagnostics(x_14);
x_44 = l_Std_PersistentArray_toArray___rarg(x_43);
x_45 = l_Lean_Server_publishDiagnostics(x_2, x_44, x_3, x_42);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_14);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_14);
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_52 = x_45;
} else {
 lean_dec_ref(x_45);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_13);
if (x_54 == 0)
{
return x_13;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_13, 0);
x_56 = lean_ctor_get(x_13, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_13);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_10);
if (x_58 == 0)
{
return x_10;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_10, 0);
x_60 = lean_ctor_get(x_10, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_10);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Server_FileWorker_CancelToken_check___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___spec__1(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_15 = x_7;
} else {
 lean_dec_ref(x_7);
 x_15 = lean_box(0);
}
if (lean_is_scalar(x_15)) {
 x_16 = lean_alloc_ctor(0, 1, 0);
} else {
 x_16 = x_15;
}
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_7);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_dec(x_6);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_inc(x_2);
x_20 = l_Lean_Server_Snapshots_Snapshot_isAtEnd(x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1(x_2, x_1, x_19, x_3, x_21, x_4, x_18);
lean_dec(x_4);
lean_dec(x_3);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_4);
lean_dec(x_3);
x_23 = l_Lean_Server_Snapshots_Snapshot_diagnostics(x_2);
x_24 = l_Std_PersistentArray_toArray___rarg(x_23);
lean_inc(x_19);
lean_inc(x_1);
x_25 = l_Lean_Server_publishDiagnostics(x_1, x_24, x_19, x_18);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_Server_publishProgressDone(x_1, x_19, x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___closed__1;
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___closed__1;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
return x_27;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_27, 0);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_27);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_19);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_25);
if (x_38 == 0)
{
return x_25;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_25, 0);
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_25);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_CancelToken_check___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_CancelToken_check___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___at_Lean_Server_FileWorker_unfoldCmdSnaps___spec__3___lambda__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
return x_8;
}
}
}
static lean_object* _init_l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___at_Lean_Server_FileWorker_unfoldCmdSnaps___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___at_Lean_Server_FileWorker_unfoldCmdSnaps___spec__3___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___at_Lean_Server_FileWorker_unfoldCmdSnaps___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___at_Lean_Server_FileWorker_unfoldCmdSnaps___spec__3___closed__1;
x_3 = l_Task_Priority_default;
x_4 = lean_task_map(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_unfoldAsync_step___at_Lean_Server_FileWorker_unfoldCmdSnaps___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = lean_apply_2(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_13 = x_5;
} else {
 lean_dec_ref(x_5);
 x_13 = lean_box(0);
}
if (lean_is_scalar(x_13)) {
 x_14 = lean_alloc_ctor(0, 1, 0);
} else {
 x_14 = x_13;
}
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
x_19 = lean_alloc_closure((void*)(l_IO_AsyncList_unfoldAsync_step___at_Lean_Server_FileWorker_unfoldCmdSnaps___spec__2), 3, 2);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = l_Task_Priority_default;
x_22 = lean_io_as_task(x_20, x_21, x_16);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_alloc_closure((void*)(l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___at_Lean_Server_FileWorker_unfoldCmdSnaps___spec__3___lambda__1), 1, 0);
x_26 = lean_task_map(x_25, x_24, x_21);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_5, 0, x_28);
lean_ctor_set(x_22, 0, x_5);
return x_22;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_22, 0);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_22);
x_31 = lean_alloc_closure((void*)(l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___at_Lean_Server_FileWorker_unfoldCmdSnaps___spec__3___lambda__1), 1, 0);
x_32 = lean_task_map(x_31, x_29, x_21);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_18);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_5, 0, x_34);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_30);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_36 = lean_ctor_get(x_5, 0);
lean_inc(x_36);
lean_dec(x_5);
lean_inc(x_36);
x_37 = lean_alloc_closure((void*)(l_IO_AsyncList_unfoldAsync_step___at_Lean_Server_FileWorker_unfoldCmdSnaps___spec__2), 3, 2);
lean_closure_set(x_37, 0, x_1);
lean_closure_set(x_37, 1, x_36);
x_38 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 1);
lean_closure_set(x_38, 0, x_37);
x_39 = l_Task_Priority_default;
x_40 = lean_io_as_task(x_38, x_39, x_16);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
x_44 = lean_alloc_closure((void*)(l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___at_Lean_Server_FileWorker_unfoldCmdSnaps___spec__3___lambda__1), 1, 0);
x_45 = lean_task_map(x_44, x_41, x_39);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
if (lean_is_scalar(x_43)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_43;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_42);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_4);
if (x_50 == 0)
{
return x_4;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_4, 0);
x_52 = lean_ctor_get(x_4, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_4);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_unfoldAsync___at_Lean_Server_FileWorker_unfoldCmdSnaps___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_alloc_closure((void*)(l_IO_AsyncList_unfoldAsync_step___at_Lean_Server_FileWorker_unfoldCmdSnaps___spec__2), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
x_5 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = l_Task_Priority_default;
x_7 = lean_io_as_task(x_5, x_6, x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___at_Lean_Server_FileWorker_unfoldCmdSnaps___spec__3___lambda__1), 1, 0);
x_11 = lean_task_map(x_10, x_9, x_6);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___at_Lean_Server_FileWorker_unfoldCmdSnaps___spec__3___lambda__1), 1, 0);
x_16 = lean_task_map(x_15, x_13, x_6);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_unfoldCmdSnaps___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap(x_1, x_4, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_unfoldCmdSnaps(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (x_4 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_unfoldCmdSnaps___lambda__1), 5, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_5);
x_8 = l_IO_AsyncList_unfoldAsync___at_Lean_Server_FileWorker_unfoldCmdSnaps___spec__1(x_7, x_2, x_6);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Server_Snapshots_Snapshot_msgLog(x_2);
x_10 = l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_unfoldCmdSnaps___lambda__1), 5, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_5);
x_12 = l_IO_AsyncList_unfoldAsync___at_Lean_Server_FileWorker_unfoldCmdSnaps___spec__1(x_11, x_2, x_6);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
lean_dec(x_3);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = 1;
x_16 = l_Lean_Server_publishProgressAtPos(x_1, x_14, x_13, x_15, x_6);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(2);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_unfoldCmdSnaps___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_Server_FileWorker_unfoldCmdSnaps(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__2;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 2;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 2);
x_9 = lean_io_prim_handle_get_line(x_8, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_14 = lean_string_dec_eq(x_11, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_9);
x_15 = lean_box(0);
x_16 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__3;
x_17 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__4;
lean_inc(x_11);
x_18 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_15);
lean_ctor_set(x_18, 4, x_15);
lean_ctor_set(x_18, 5, x_11);
lean_ctor_set(x_18, 6, x_15);
lean_ctor_set(x_18, 7, x_15);
x_19 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__5;
x_20 = lean_array_push(x_19, x_18);
lean_inc(x_3);
lean_inc(x_2);
x_21 = l_Lean_Server_publishDiagnostics(x_2, x_20, x_3, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_string_append(x_6, x_11);
lean_dec(x_11);
x_6 = x_23;
x_7 = x_22;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_9, 0, x_6);
return x_9;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_9, 0);
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_9);
x_31 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_32 = lean_string_dec_eq(x_29, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_box(0);
x_34 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__3;
x_35 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__4;
lean_inc(x_29);
x_36 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set(x_36, 3, x_33);
lean_ctor_set(x_36, 4, x_33);
lean_ctor_set(x_36, 5, x_29);
lean_ctor_set(x_36, 6, x_33);
lean_ctor_set(x_36, 7, x_33);
x_37 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__5;
x_38 = lean_array_push(x_37, x_36);
lean_inc(x_3);
lean_inc(x_2);
x_39 = l_Lean_Server_publishDiagnostics(x_2, x_38, x_3, x_30);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_string_append(x_6, x_29);
lean_dec(x_29);
x_6 = x_41;
x_7 = x_40;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_45 = x_39;
} else {
 lean_dec_ref(x_39);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; 
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_6);
lean_ctor_set(x_47, 1, x_30);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_9);
if (x_48 == 0)
{
return x_9;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_9, 0);
x_50 = lean_ctor_get(x_9, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_9);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 1;
x_10 = l_Lean_Name_toString(x_8, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_13 = lean_array_uset(x_7, x_2, x_10);
x_2 = x_12;
x_3 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_mapM___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = l_Lean_realPathNormalized(x_6, x_2);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_List_mapM___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__2(x_7, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_9);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_1, 1, x_14);
lean_ctor_set(x_1, 0, x_9);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_9);
lean_free_object(x_1);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_free_object(x_1);
lean_dec(x_7);
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
return x_8;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_8);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_1);
x_27 = l_Lean_realPathNormalized(x_25, x_2);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_List_mapM___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__2(x_26, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_31);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_28);
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_38 = x_30;
} else {
 lean_dec_ref(x_30);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_26);
x_40 = lean_ctor_get(x_27, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_27, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_42 = x_27;
} else {
 lean_dec_ref(x_27);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("print-paths");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__5;
x_2 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" ");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__4() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; 
x_1 = 2;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, 1, x_2);
lean_ctor_set_uint8(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("`");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("` failed:\n");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nstderr:\n");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid output from `");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("`:\n");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_8 = 0;
x_9 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__1(x_7, x_8, x_3);
x_10 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__2;
x_11 = l_Array_append___rarg(x_10, x_9);
lean_inc(x_11);
x_12 = lean_array_to_list(lean_box(0), x_11);
lean_inc(x_1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__3;
x_15 = l_String_intercalate(x_14, x_13);
x_16 = lean_box(0);
x_17 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__4;
x_18 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__5;
lean_inc(x_11);
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set(x_19, 2, x_11);
lean_ctor_set(x_19, 3, x_16);
lean_ctor_set(x_19, 4, x_18);
x_20 = lean_io_process_spawn(x_19, x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
lean_inc(x_21);
x_24 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___boxed), 7, 6);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_2);
lean_closure_set(x_24, 2, x_4);
lean_closure_set(x_24, 3, x_11);
lean_closure_set(x_24, 4, x_21);
lean_closure_set(x_24, 5, x_23);
x_25 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = l_Task_Priority_dedicated;
x_27 = lean_io_as_task(x_25, x_26, x_22);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
x_31 = l_IO_FS_Handle_readToEnd_loop(x_30, x_23, x_29);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_String_trim(x_32);
lean_dec(x_32);
x_35 = lean_task_get_own(x_28);
x_36 = l_IO_ofExcept___at_IO_Process_output___spec__1(x_35, x_33);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_io_process_child_wait(x_17, x_21, x_38);
lean_dec(x_21);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint32_t x_43; uint32_t x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
x_43 = 0;
x_44 = lean_unbox_uint32(x_41);
x_45 = lean_uint32_dec_eq(x_44, x_43);
if (x_45 == 0)
{
uint32_t x_46; uint32_t x_47; uint8_t x_48; 
x_46 = 2;
x_47 = lean_unbox_uint32(x_41);
lean_dec(x_41);
x_48 = lean_uint32_dec_eq(x_47, x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_free_object(x_39);
x_49 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__6;
x_50 = lean_string_append(x_49, x_15);
lean_dec(x_15);
x_51 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__7;
x_52 = lean_string_append(x_50, x_51);
x_53 = lean_string_append(x_52, x_34);
lean_dec(x_34);
x_54 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__8;
x_55 = lean_string_append(x_53, x_54);
x_56 = lean_string_append(x_55, x_37);
lean_dec(x_37);
x_57 = lean_string_append(x_56, x_23);
x_58 = l_IO_throwServerError___rarg(x_57, x_42);
return x_58;
}
else
{
lean_object* x_59; 
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_15);
x_59 = lean_box(0);
lean_ctor_set(x_39, 0, x_59);
return x_39;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_free_object(x_39);
lean_dec(x_41);
x_60 = l_String_split___at_Lean_stringToMessageData___spec__1(x_34);
lean_dec(x_34);
x_61 = l_String_instInhabitedString;
x_62 = l_List_getLast_x21___rarg(x_61, x_60);
lean_inc(x_62);
x_63 = l_Lean_Json_parse(x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_63);
x_64 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__9;
x_65 = lean_string_append(x_64, x_15);
lean_dec(x_15);
x_66 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__10;
x_67 = lean_string_append(x_65, x_66);
x_68 = lean_string_append(x_67, x_62);
lean_dec(x_62);
x_69 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__8;
x_70 = lean_string_append(x_68, x_69);
x_71 = lean_string_append(x_70, x_37);
lean_dec(x_37);
x_72 = lean_string_append(x_71, x_23);
x_73 = l_IO_throwServerError___rarg(x_72, x_42);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_63, 0);
lean_inc(x_74);
lean_dec(x_63);
x_75 = l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63_(x_74);
lean_dec(x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_75);
x_76 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__9;
x_77 = lean_string_append(x_76, x_15);
lean_dec(x_15);
x_78 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__10;
x_79 = lean_string_append(x_77, x_78);
x_80 = lean_string_append(x_79, x_62);
lean_dec(x_62);
x_81 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__8;
x_82 = lean_string_append(x_80, x_81);
x_83 = lean_string_append(x_82, x_37);
lean_dec(x_37);
x_84 = lean_string_append(x_83, x_23);
x_85 = l_IO_throwServerError___rarg(x_84, x_42);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_62);
lean_dec(x_37);
lean_dec(x_15);
x_86 = lean_ctor_get(x_75, 0);
lean_inc(x_86);
lean_dec(x_75);
x_87 = lean_get_prefix(x_42);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_ctor_get(x_86, 0);
lean_inc(x_90);
x_91 = l_Lean_initSearchPath(x_88, x_90, x_89);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
x_93 = lean_ctor_get(x_86, 1);
lean_inc(x_93);
lean_dec(x_86);
x_94 = l_List_mapM___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__2(x_93, x_92);
return x_94;
}
else
{
uint8_t x_95; 
lean_dec(x_86);
x_95 = !lean_is_exclusive(x_91);
if (x_95 == 0)
{
return x_91;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_91, 0);
x_97 = lean_ctor_get(x_91, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_91);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_86);
x_99 = !lean_is_exclusive(x_87);
if (x_99 == 0)
{
return x_87;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_87, 0);
x_101 = lean_ctor_get(x_87, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_87);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
}
}
else
{
lean_object* x_103; lean_object* x_104; uint32_t x_105; uint32_t x_106; uint8_t x_107; 
x_103 = lean_ctor_get(x_39, 0);
x_104 = lean_ctor_get(x_39, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_39);
x_105 = 0;
x_106 = lean_unbox_uint32(x_103);
x_107 = lean_uint32_dec_eq(x_106, x_105);
if (x_107 == 0)
{
uint32_t x_108; uint32_t x_109; uint8_t x_110; 
x_108 = 2;
x_109 = lean_unbox_uint32(x_103);
lean_dec(x_103);
x_110 = lean_uint32_dec_eq(x_109, x_108);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_111 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__6;
x_112 = lean_string_append(x_111, x_15);
lean_dec(x_15);
x_113 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__7;
x_114 = lean_string_append(x_112, x_113);
x_115 = lean_string_append(x_114, x_34);
lean_dec(x_34);
x_116 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__8;
x_117 = lean_string_append(x_115, x_116);
x_118 = lean_string_append(x_117, x_37);
lean_dec(x_37);
x_119 = lean_string_append(x_118, x_23);
x_120 = l_IO_throwServerError___rarg(x_119, x_104);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_15);
x_121 = lean_box(0);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_104);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_103);
x_123 = l_String_split___at_Lean_stringToMessageData___spec__1(x_34);
lean_dec(x_34);
x_124 = l_String_instInhabitedString;
x_125 = l_List_getLast_x21___rarg(x_124, x_123);
lean_inc(x_125);
x_126 = l_Lean_Json_parse(x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_126);
x_127 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__9;
x_128 = lean_string_append(x_127, x_15);
lean_dec(x_15);
x_129 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__10;
x_130 = lean_string_append(x_128, x_129);
x_131 = lean_string_append(x_130, x_125);
lean_dec(x_125);
x_132 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__8;
x_133 = lean_string_append(x_131, x_132);
x_134 = lean_string_append(x_133, x_37);
lean_dec(x_37);
x_135 = lean_string_append(x_134, x_23);
x_136 = l_IO_throwServerError___rarg(x_135, x_104);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_126, 0);
lean_inc(x_137);
lean_dec(x_126);
x_138 = l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63_(x_137);
lean_dec(x_137);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_138);
x_139 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__9;
x_140 = lean_string_append(x_139, x_15);
lean_dec(x_15);
x_141 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__10;
x_142 = lean_string_append(x_140, x_141);
x_143 = lean_string_append(x_142, x_125);
lean_dec(x_125);
x_144 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__8;
x_145 = lean_string_append(x_143, x_144);
x_146 = lean_string_append(x_145, x_37);
lean_dec(x_37);
x_147 = lean_string_append(x_146, x_23);
x_148 = l_IO_throwServerError___rarg(x_147, x_104);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_125);
lean_dec(x_37);
lean_dec(x_15);
x_149 = lean_ctor_get(x_138, 0);
lean_inc(x_149);
lean_dec(x_138);
x_150 = lean_get_prefix(x_104);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_ctor_get(x_149, 0);
lean_inc(x_153);
x_154 = l_Lean_initSearchPath(x_151, x_153, x_152);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec(x_154);
x_156 = lean_ctor_get(x_149, 1);
lean_inc(x_156);
lean_dec(x_149);
x_157 = l_List_mapM___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__2(x_156, x_155);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_149);
x_158 = lean_ctor_get(x_154, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_154, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_160 = x_154;
} else {
 lean_dec_ref(x_154);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_159);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_149);
x_162 = lean_ctor_get(x_150, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_150, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_164 = x_150;
} else {
 lean_dec_ref(x_150);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
}
}
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_15);
x_166 = !lean_is_exclusive(x_39);
if (x_166 == 0)
{
return x_39;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_39, 0);
x_168 = lean_ctor_get(x_39, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_39);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_34);
lean_dec(x_21);
lean_dec(x_15);
x_170 = !lean_is_exclusive(x_36);
if (x_170 == 0)
{
return x_36;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_36, 0);
x_172 = lean_ctor_get(x_36, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_36);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
else
{
uint8_t x_174; 
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_15);
x_174 = !lean_is_exclusive(x_31);
if (x_174 == 0)
{
return x_31;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_31, 0);
x_176 = lean_ctor_get(x_31, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_31);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
else
{
uint8_t x_178; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_178 = !lean_is_exclusive(x_20);
if (x_178 == 0)
{
return x_20;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_20, 0);
x_180 = lean_ctor_get(x_20, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_20);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_8 = lean_array_uget(x_4, x_3);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_4, x_3, x_9);
lean_inc(x_1);
x_11 = l_Std_PersistentArray_mapMAux___at_Lean_Server_FileWorker_compileHeader___spec__2(x_1, x_8, x_5);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_16 = lean_array_uset(x_10, x_3, x_12);
x_3 = x_15;
x_4 = x_16;
x_5 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_8 = lean_array_uget(x_4, x_3);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_4, x_3, x_9);
lean_inc(x_1);
x_11 = l_Lean_Widget_msgToInteractiveDiagnostic(x_1, x_8, x_5);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_16 = lean_array_uset(x_10, x_3, x_12);
x_3 = x_15;
x_4 = x_16;
x_5 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapMAux___at_Lean_Server_FileWorker_compileHeader___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_array_get_size(x_5);
x_7 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_8 = 0;
x_9 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__3(x_1, x_7, x_8, x_5, x_3);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_ctor_set(x_2, 0, x_11);
lean_ctor_set(x_9, 0, x_2);
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_9);
lean_ctor_set(x_2, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_array_get_size(x_15);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__3(x_1, x_17, x_18, x_15, x_3);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_22 = x_19;
} else {
 lean_dec_ref(x_19);
 x_22 = lean_box(0);
}
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
if (lean_is_scalar(x_22)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_22;
}
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_2);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_array_get_size(x_26);
x_28 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_29 = 0;
x_30 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__4(x_1, x_28, x_29, x_26, x_3);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_ctor_set(x_2, 0, x_32);
lean_ctor_set(x_30, 0, x_2);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_30);
lean_ctor_set(x_2, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_36 = lean_ctor_get(x_2, 0);
lean_inc(x_36);
lean_dec(x_2);
x_37 = lean_array_get_size(x_36);
x_38 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_39 = 0;
x_40 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__4(x_1, x_38, x_39, x_36, x_3);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_41);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_8 = lean_array_uget(x_4, x_3);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_4, x_3, x_9);
lean_inc(x_1);
x_11 = l_Lean_Widget_msgToInteractiveDiagnostic(x_1, x_8, x_5);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_16 = lean_array_uset(x_10, x_3, x_12);
x_3 = x_15;
x_4 = x_16;
x_5 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapM___at_Lean_Server_FileWorker_compileHeader___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = l_Std_PersistentArray_mapMAux___at_Lean_Server_FileWorker_compileHeader___spec__2(x_1, x_5, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_array_get_size(x_6);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = 0;
x_13 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__5(x_1, x_11, x_12, x_6, x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_ctor_set(x_2, 1, x_15);
lean_ctor_set(x_2, 0, x_8);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_13);
lean_ctor_set(x_2, 1, x_16);
lean_ctor_set(x_2, 0, x_8);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_2, 2);
x_22 = lean_ctor_get_usize(x_2, 4);
x_23 = lean_ctor_get(x_2, 3);
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_2);
lean_inc(x_1);
x_24 = l_Std_PersistentArray_mapMAux___at_Lean_Server_FileWorker_compileHeader___spec__2(x_1, x_19, x_3);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_array_get_size(x_20);
x_28 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_29 = 0;
x_30 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__5(x_1, x_28, x_29, x_20, x_26);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_21);
lean_ctor_set(x_34, 3, x_23);
lean_ctor_set_usize(x_34, 4, x_22);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_8 = lean_array_uget(x_4, x_3);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_4, x_3, x_9);
lean_inc(x_1);
x_11 = l_Std_PersistentArray_mapMAux___at_Lean_Server_FileWorker_compileHeader___spec__7(x_1, x_8, x_5);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_16 = lean_array_uset(x_10, x_3, x_12);
x_3 = x_15;
x_4 = x_16;
x_5 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__9(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_8 = lean_array_uget(x_4, x_3);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_4, x_3, x_9);
lean_inc(x_1);
x_11 = l_Lean_Widget_msgToInteractiveDiagnostic(x_1, x_8, x_5);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_16 = lean_array_uset(x_10, x_3, x_12);
x_3 = x_15;
x_4 = x_16;
x_5 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapMAux___at_Lean_Server_FileWorker_compileHeader___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_array_get_size(x_5);
x_7 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_8 = 0;
x_9 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__8(x_1, x_7, x_8, x_5, x_3);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_ctor_set(x_2, 0, x_11);
lean_ctor_set(x_9, 0, x_2);
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_9);
lean_ctor_set(x_2, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_array_get_size(x_15);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__8(x_1, x_17, x_18, x_15, x_3);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_22 = x_19;
} else {
 lean_dec_ref(x_19);
 x_22 = lean_box(0);
}
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
if (lean_is_scalar(x_22)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_22;
}
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_2);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_array_get_size(x_26);
x_28 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_29 = 0;
x_30 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__9(x_1, x_28, x_29, x_26, x_3);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_ctor_set(x_2, 0, x_32);
lean_ctor_set(x_30, 0, x_2);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_30);
lean_ctor_set(x_2, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_36 = lean_ctor_get(x_2, 0);
lean_inc(x_36);
lean_dec(x_2);
x_37 = lean_array_get_size(x_36);
x_38 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_39 = 0;
x_40 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__9(x_1, x_38, x_39, x_36, x_3);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_41);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_8 = lean_array_uget(x_4, x_3);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_4, x_3, x_9);
lean_inc(x_1);
x_11 = l_Lean_Widget_msgToInteractiveDiagnostic(x_1, x_8, x_5);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_16 = lean_array_uset(x_10, x_3, x_12);
x_3 = x_15;
x_4 = x_16;
x_5 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapM___at_Lean_Server_FileWorker_compileHeader___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = l_Std_PersistentArray_mapMAux___at_Lean_Server_FileWorker_compileHeader___spec__7(x_1, x_5, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_array_get_size(x_6);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = 0;
x_13 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__10(x_1, x_11, x_12, x_6, x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_ctor_set(x_2, 1, x_15);
lean_ctor_set(x_2, 0, x_8);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_13);
lean_ctor_set(x_2, 1, x_16);
lean_ctor_set(x_2, 0, x_8);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_2, 2);
x_22 = lean_ctor_get_usize(x_2, 4);
x_23 = lean_ctor_get(x_2, 3);
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_2);
lean_inc(x_1);
x_24 = l_Std_PersistentArray_mapMAux___at_Lean_Server_FileWorker_compileHeader___spec__7(x_1, x_19, x_3);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_array_get_size(x_20);
x_28 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_29 = 0;
x_30 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__10(x_1, x_28, x_29, x_20, x_26);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_21);
lean_ctor_set(x_34, 3, x_23);
lean_ctor_set_usize(x_34, 4, x_22);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_firstFrontendMacroScope;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("import");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__5;
x_2 = l_Array_toPersistentArray___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Lean_Elab_Command_mkState(x_1, x_2, x_3);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_14 = lean_ctor_get(x_12, 7);
lean_dec(x_14);
x_15 = lean_ctor_get(x_12, 5);
lean_dec(x_15);
x_16 = lean_ctor_get(x_12, 4);
lean_dec(x_16);
x_17 = lean_ctor_get(x_12, 3);
lean_dec(x_17);
x_18 = lean_ctor_get(x_12, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_12, 0);
lean_dec(x_19);
x_20 = l_Lean_maxRecDepth;
x_21 = l_Lean_Option_get___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_245____spec__1(x_3, x_20);
lean_dec(x_3);
x_22 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__6;
lean_inc(x_4);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_4);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__7;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__5;
x_28 = lean_array_push(x_27, x_26);
x_29 = l_Array_toPersistentArray___rarg(x_28);
lean_dec(x_28);
x_30 = 1;
x_31 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__4;
x_32 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_30);
x_33 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__1;
x_34 = lean_unsigned_to_nat(1u);
lean_inc(x_2);
lean_ctor_set(x_12, 7, x_32);
lean_ctor_set(x_12, 5, x_34);
lean_ctor_set(x_12, 4, x_21);
lean_ctor_set(x_12, 3, x_33);
lean_ctor_set(x_12, 1, x_2);
lean_ctor_set(x_12, 0, x_1);
x_35 = l_Std_PersistentArray_mapM___at_Lean_Server_FileWorker_compileHeader___spec__1(x_5, x_2, x_11);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_4);
lean_ctor_set(x_39, 2, x_6);
lean_ctor_set(x_39, 3, x_12);
lean_ctor_set(x_39, 4, x_36);
lean_inc(x_39);
x_40 = l_Lean_Server_Snapshots_Snapshot_diagnostics(x_39);
x_41 = l_Std_PersistentArray_toArray___rarg(x_40);
x_42 = l_Lean_Server_publishDiagnostics(x_7, x_41, x_8, x_37);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_9);
lean_ctor_set(x_42, 0, x_45);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_39);
lean_ctor_set(x_47, 1, x_9);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_39);
lean_dec(x_9);
x_49 = !lean_is_exclusive(x_42);
if (x_49 == 0)
{
return x_42;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_42, 0);
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_42);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_53 = lean_ctor_get(x_12, 2);
x_54 = lean_ctor_get(x_12, 6);
x_55 = lean_ctor_get(x_12, 8);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_12);
x_56 = l_Lean_maxRecDepth;
x_57 = l_Lean_Option_get___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_245____spec__1(x_3, x_56);
lean_dec(x_3);
x_58 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__6;
lean_inc(x_4);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_4);
x_60 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__7;
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__5;
x_64 = lean_array_push(x_63, x_62);
x_65 = l_Array_toPersistentArray___rarg(x_64);
lean_dec(x_64);
x_66 = 1;
x_67 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__4;
x_68 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
lean_ctor_set_uint8(x_68, sizeof(void*)*2, x_66);
x_69 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__1;
x_70 = lean_unsigned_to_nat(1u);
lean_inc(x_2);
x_71 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_71, 0, x_1);
lean_ctor_set(x_71, 1, x_2);
lean_ctor_set(x_71, 2, x_53);
lean_ctor_set(x_71, 3, x_69);
lean_ctor_set(x_71, 4, x_57);
lean_ctor_set(x_71, 5, x_70);
lean_ctor_set(x_71, 6, x_54);
lean_ctor_set(x_71, 7, x_68);
lean_ctor_set(x_71, 8, x_55);
x_72 = l_Std_PersistentArray_mapM___at_Lean_Server_FileWorker_compileHeader___spec__1(x_5, x_2, x_11);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_4);
lean_ctor_set(x_76, 2, x_6);
lean_ctor_set(x_76, 3, x_71);
lean_ctor_set(x_76, 4, x_73);
lean_inc(x_76);
x_77 = l_Lean_Server_Snapshots_Snapshot_diagnostics(x_76);
x_78 = l_Std_PersistentArray_toArray___rarg(x_77);
x_79 = l_Lean_Server_publishDiagnostics(x_7, x_78, x_8, x_74);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_81 = x_79;
} else {
 lean_dec_ref(x_79);
 x_81 = lean_box(0);
}
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_76);
lean_ctor_set(x_82, 1, x_9);
if (lean_is_scalar(x_81)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_81;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_80);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_76);
lean_dec(x_9);
x_84 = lean_ctor_get(x_79, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_79, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_86 = x_79;
} else {
 lean_dec_ref(x_79);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Lean_Elab_Command_mkState(x_1, x_2, x_3);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_14 = lean_ctor_get(x_12, 7);
lean_dec(x_14);
x_15 = lean_ctor_get(x_12, 5);
lean_dec(x_15);
x_16 = lean_ctor_get(x_12, 4);
lean_dec(x_16);
x_17 = lean_ctor_get(x_12, 3);
lean_dec(x_17);
x_18 = lean_ctor_get(x_12, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_12, 0);
lean_dec(x_19);
x_20 = l_Lean_maxRecDepth;
x_21 = l_Lean_Option_get___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_245____spec__1(x_3, x_20);
lean_dec(x_3);
x_22 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__6;
lean_inc(x_4);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_4);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__7;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__5;
x_28 = lean_array_push(x_27, x_26);
x_29 = l_Array_toPersistentArray___rarg(x_28);
lean_dec(x_28);
x_30 = 1;
x_31 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__4;
x_32 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_30);
x_33 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__1;
x_34 = lean_unsigned_to_nat(1u);
lean_inc(x_2);
lean_ctor_set(x_12, 7, x_32);
lean_ctor_set(x_12, 5, x_34);
lean_ctor_set(x_12, 4, x_21);
lean_ctor_set(x_12, 3, x_33);
lean_ctor_set(x_12, 1, x_2);
lean_ctor_set(x_12, 0, x_1);
x_35 = l_Std_PersistentArray_mapM___at_Lean_Server_FileWorker_compileHeader___spec__6(x_5, x_2, x_11);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_4);
lean_ctor_set(x_39, 2, x_6);
lean_ctor_set(x_39, 3, x_12);
lean_ctor_set(x_39, 4, x_36);
lean_inc(x_39);
x_40 = l_Lean_Server_Snapshots_Snapshot_diagnostics(x_39);
x_41 = l_Std_PersistentArray_toArray___rarg(x_40);
x_42 = l_Lean_Server_publishDiagnostics(x_7, x_41, x_8, x_37);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_9);
lean_ctor_set(x_42, 0, x_45);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_39);
lean_ctor_set(x_47, 1, x_9);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_39);
lean_dec(x_9);
x_49 = !lean_is_exclusive(x_42);
if (x_49 == 0)
{
return x_42;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_42, 0);
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_42);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_53 = lean_ctor_get(x_12, 2);
x_54 = lean_ctor_get(x_12, 6);
x_55 = lean_ctor_get(x_12, 8);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_12);
x_56 = l_Lean_maxRecDepth;
x_57 = l_Lean_Option_get___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_245____spec__1(x_3, x_56);
lean_dec(x_3);
x_58 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__6;
lean_inc(x_4);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_4);
x_60 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__7;
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__5;
x_64 = lean_array_push(x_63, x_62);
x_65 = l_Array_toPersistentArray___rarg(x_64);
lean_dec(x_64);
x_66 = 1;
x_67 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__4;
x_68 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
lean_ctor_set_uint8(x_68, sizeof(void*)*2, x_66);
x_69 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__1;
x_70 = lean_unsigned_to_nat(1u);
lean_inc(x_2);
x_71 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_71, 0, x_1);
lean_ctor_set(x_71, 1, x_2);
lean_ctor_set(x_71, 2, x_53);
lean_ctor_set(x_71, 3, x_69);
lean_ctor_set(x_71, 4, x_57);
lean_ctor_set(x_71, 5, x_70);
lean_ctor_set(x_71, 6, x_54);
lean_ctor_set(x_71, 7, x_68);
lean_ctor_set(x_71, 8, x_55);
x_72 = l_Std_PersistentArray_mapM___at_Lean_Server_FileWorker_compileHeader___spec__6(x_5, x_2, x_11);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_4);
lean_ctor_set(x_76, 2, x_6);
lean_ctor_set(x_76, 3, x_71);
lean_ctor_set(x_76, 4, x_73);
lean_inc(x_76);
x_77 = l_Lean_Server_Snapshots_Snapshot_diagnostics(x_76);
x_78 = l_Std_PersistentArray_toArray___rarg(x_77);
x_79 = l_Lean_Server_publishDiagnostics(x_7, x_78, x_8, x_74);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_81 = x_79;
} else {
 lean_dec_ref(x_79);
 x_81 = lean_box(0);
}
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_76);
lean_ctor_set(x_82, 1, x_9);
if (lean_is_scalar(x_81)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_81;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_80);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_76);
lean_dec(x_9);
x_84 = lean_ctor_get(x_79, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_79, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_86 = x_79;
} else {
 lean_dec_ref(x_79);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("LEAN_SRC_PATH");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_28; lean_object* x_29; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_28 = lean_ctor_get(x_5, 0);
lean_inc(x_28);
x_29 = l_Lean_Lsp_DocumentUri_toPath_x3f(x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__1;
x_31 = lean_io_getenv(x_30, x_9);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_box(0);
x_35 = l_Lean_Server_FileWorker_compileHeader___lambda__2(x_10, x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_34, x_33);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_ctor_get(x_32, 0);
lean_inc(x_37);
lean_dec(x_32);
x_38 = l_System_SearchPath_parse(x_37);
x_39 = l_List_appendTR___rarg(x_38, x_7);
x_40 = lean_box(0);
x_41 = l_Lean_Server_FileWorker_compileHeader___lambda__2(x_10, x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_39, x_40, x_36);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_29, 0);
lean_inc(x_42);
lean_dec(x_29);
x_43 = lean_box(0);
x_44 = lean_module_name_of_file(x_42, x_43, x_9);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_environment_set_main_module(x_10, x_45);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_12 = x_49;
x_13 = x_46;
goto block_27;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_dec(x_44);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_10);
x_12 = x_52;
x_13 = x_50;
goto block_27;
}
}
block_27:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__1;
x_16 = lean_io_getenv(x_15, x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = l_Lean_Server_FileWorker_compileHeader___lambda__1(x_14, x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_19, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = l_System_SearchPath_parse(x_22);
x_24 = l_List_appendTR___rarg(x_23, x_7);
x_25 = lean_box(0);
x_26 = l_Lean_Server_FileWorker_compileHeader___lambda__1(x_14, x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_24, x_25, x_21);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint32_t x_8; lean_object* x_9; 
x_8 = 0;
x_9 = l_Lean_Elab_processHeader(x_1, x_2, x_3, x_4, x_8, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_5);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_5);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("..");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lib");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("src");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lake");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<ignored>");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lakefile.lean");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__8;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_appDir(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_38; lean_object* x_39; lean_object* x_62; lean_object* x_63; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__1;
x_15 = l_System_FilePath_join(x_12, x_14);
x_16 = l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__2;
x_17 = l_System_FilePath_join(x_15, x_16);
x_18 = l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__3;
x_19 = l_System_FilePath_join(x_17, x_18);
x_20 = l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__4;
x_21 = l_System_FilePath_join(x_19, x_20);
x_22 = l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__5;
lean_inc(x_21);
x_23 = l_System_FilePath_join(x_21, x_22);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_62 = lean_ctor_get(x_5, 0);
lean_inc(x_62);
x_63 = l_Lean_Lsp_DocumentUri_toPath_x3f(x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_9);
x_64 = lean_box(0);
lean_inc(x_26);
lean_inc(x_1);
x_65 = l_Lean_Server_FileWorker_compileHeader___lambda__4(x_2, x_1, x_7, x_8, x_26, x_64, x_13);
lean_dec(x_8);
if (lean_obj_tag(x_65) == 0)
{
lean_dec(x_26);
x_27 = x_65;
goto block_37;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_38 = x_66;
x_39 = x_67;
goto block_61;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_68 = lean_ctor_get(x_63, 0);
lean_inc(x_68);
lean_dec(x_63);
x_69 = l_System_FilePath_pathExists(x_9, x_13);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_System_FilePath_fileName(x_68);
x_73 = l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__9;
x_74 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_802____at___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_beqDiagnosticWith____x40_Lean_Data_Lsp_Diagnostics___hyg_703____spec__3(x_72, x_73);
lean_dec(x_72);
if (x_74 == 0)
{
uint8_t x_75; 
x_75 = lean_unbox(x_70);
lean_dec(x_70);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_9);
x_76 = lean_box(0);
lean_inc(x_26);
lean_inc(x_1);
x_77 = l_Lean_Server_FileWorker_compileHeader___lambda__4(x_2, x_1, x_7, x_8, x_26, x_76, x_71);
lean_dec(x_8);
if (lean_obj_tag(x_77) == 0)
{
lean_dec(x_26);
x_27 = x_77;
goto block_37;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_38 = x_78;
x_39 = x_79;
goto block_61;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = l_Lean_Elab_headerToImports(x_2);
x_81 = l_List_redLength___rarg(x_80);
x_82 = lean_mk_empty_array_with_capacity(x_81);
lean_dec(x_81);
x_83 = l_List_toArrayAux___rarg(x_80, x_82);
lean_inc(x_6);
lean_inc(x_5);
x_84 = l_Lean_Server_FileWorker_lakeSetupSearchPath(x_9, x_5, x_83, x_6, x_71);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
lean_inc(x_26);
x_87 = l_List_appendTR___rarg(x_85, x_26);
x_88 = lean_box(0);
lean_inc(x_1);
x_89 = l_Lean_Server_FileWorker_compileHeader___lambda__4(x_2, x_1, x_7, x_8, x_87, x_88, x_86);
lean_dec(x_8);
if (lean_obj_tag(x_89) == 0)
{
lean_dec(x_26);
x_27 = x_89;
goto block_37;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_38 = x_90;
x_39 = x_91;
goto block_61;
}
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_8);
lean_dec(x_7);
x_92 = lean_ctor_get(x_84, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_84, 1);
lean_inc(x_93);
lean_dec(x_84);
x_38 = x_92;
x_39 = x_93;
goto block_61;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_70);
lean_dec(x_9);
x_94 = lean_box(0);
lean_inc(x_26);
lean_inc(x_1);
x_95 = l_Lean_Server_FileWorker_compileHeader___lambda__4(x_2, x_1, x_7, x_8, x_26, x_94, x_71);
lean_dec(x_8);
if (lean_obj_tag(x_95) == 0)
{
lean_dec(x_26);
x_27 = x_95;
goto block_37;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_38 = x_96;
x_39 = x_97;
goto block_61;
}
}
}
block_37:
{
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Lean_Server_FileWorker_compileHeader___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_30, x_31, x_29);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_27, 0);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_27);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
block_61:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint32_t x_51; lean_object* x_52; 
x_40 = lean_box(0);
x_41 = lean_io_error_to_string(x_38);
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__7;
x_45 = l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__6;
x_46 = 2;
x_47 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_48 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_45);
lean_ctor_set(x_48, 2, x_40);
lean_ctor_set(x_48, 3, x_47);
lean_ctor_set(x_48, 4, x_43);
lean_ctor_set_uint8(x_48, sizeof(void*)*5, x_46);
x_49 = l_Lean_MessageLog_empty;
x_50 = l_Std_PersistentArray_push___rarg(x_49, x_48);
x_51 = 0;
x_52 = lean_mk_empty_environment(x_51, x_39);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_50);
x_56 = l_Lean_Server_FileWorker_compileHeader___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_26, x_55, x_54);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_50);
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
return x_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_52, 0);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_52);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_11);
if (x_98 == 0)
{
return x_11;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_11, 0);
x_100 = lean_ctor_get(x_11, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_11);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_System_FilePath_exeExtension;
x_5 = l_System_FilePath_withExtension(x_2, x_4);
x_6 = lean_apply_2(x_1, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<input>");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("LAKE");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("leanpkg.toml");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("LEAN_SYSROOT");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("bin");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("leanpkg");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = l_Lean_Server_FileWorker_compileHeader___closed__1;
x_8 = l_Lean_Parser_mkInputContext(x_6, x_7);
lean_inc(x_8);
x_9 = l_Lean_Parser_parseHeader(x_8, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = l_Lean_Server_FileWorker_compileHeader___closed__2;
x_17 = lean_io_getenv(x_16, x_12);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_52; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_compileHeader___lambda__5), 10, 8);
lean_closure_set(x_20, 0, x_3);
lean_closure_set(x_20, 1, x_13);
lean_closure_set(x_20, 2, x_5);
lean_closure_set(x_20, 3, x_14);
lean_closure_set(x_20, 4, x_1);
lean_closure_set(x_20, 5, x_2);
lean_closure_set(x_20, 6, x_15);
lean_closure_set(x_20, 7, x_8);
x_21 = l_Lean_Server_FileWorker_compileHeader___closed__3;
x_22 = l_System_FilePath_pathExists(x_21, x_19);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__8;
x_26 = l_System_FilePath_pathExists(x_25, x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Server_FileWorker_compileHeader___closed__4;
x_30 = lean_io_getenv(x_29, x_28);
x_52 = lean_unbox(x_23);
lean_dec(x_23);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_27);
x_53 = lean_box(0);
x_31 = x_53;
goto block_51;
}
else
{
uint8_t x_54; 
x_54 = lean_unbox(x_27);
lean_dec(x_27);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_30, 0);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_30, 1);
lean_inc(x_56);
lean_dec(x_30);
x_57 = l_IO_appDir(x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_Server_FileWorker_compileHeader___closed__6;
x_61 = l_System_FilePath_join(x_58, x_60);
x_62 = l_Lean_Server_FileWorker_compileHeader___lambda__6(x_20, x_61, x_59);
return x_62;
}
else
{
uint8_t x_63; 
lean_dec(x_20);
x_63 = !lean_is_exclusive(x_57);
if (x_63 == 0)
{
return x_57;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_57, 0);
x_65 = lean_ctor_get(x_57, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_57);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = lean_ctor_get(x_30, 1);
lean_inc(x_67);
lean_dec(x_30);
x_68 = lean_ctor_get(x_55, 0);
lean_inc(x_68);
lean_dec(x_55);
x_69 = l_Lean_Server_FileWorker_compileHeader___closed__5;
x_70 = l_System_FilePath_join(x_68, x_69);
x_71 = l_Lean_Server_FileWorker_compileHeader___closed__6;
x_72 = l_System_FilePath_join(x_70, x_71);
x_73 = l_Lean_Server_FileWorker_compileHeader___lambda__6(x_20, x_72, x_67);
return x_73;
}
}
else
{
lean_object* x_74; 
x_74 = lean_box(0);
x_31 = x_74;
goto block_51;
}
}
block_51:
{
lean_object* x_32; 
lean_dec(x_31);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = l_IO_appDir(x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__5;
x_38 = l_System_FilePath_join(x_35, x_37);
x_39 = l_Lean_Server_FileWorker_compileHeader___lambda__6(x_20, x_38, x_36);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_20);
x_40 = !lean_is_exclusive(x_34);
if (x_40 == 0)
{
return x_34;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_34, 0);
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_34);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_30, 1);
lean_inc(x_44);
lean_dec(x_30);
x_45 = lean_ctor_get(x_32, 0);
lean_inc(x_45);
lean_dec(x_32);
x_46 = l_Lean_Server_FileWorker_compileHeader___closed__5;
x_47 = l_System_FilePath_join(x_45, x_46);
x_48 = l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__5;
x_49 = l_System_FilePath_join(x_47, x_48);
x_50 = l_Lean_Server_FileWorker_compileHeader___lambda__6(x_20, x_49, x_44);
return x_50;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_17, 1);
lean_inc(x_75);
lean_dec(x_17);
x_76 = lean_ctor_get(x_18, 0);
lean_inc(x_76);
lean_dec(x_18);
x_77 = l_Lean_Server_FileWorker_compileHeader___lambda__5(x_3, x_13, x_5, x_14, x_1, x_2, x_15, x_8, x_76, x_75);
return x_77;
}
}
else
{
uint8_t x_78; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_9);
if (x_78 == 0)
{
return x_9;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_9, 0);
x_80 = lean_ctor_get(x_9, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_9);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__3(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__4(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__5(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__8(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__9(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__10(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Server_FileWorker_compileHeader___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Server_FileWorker_compileHeader___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_FileWorker_compileHeader___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initializeWorker(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_3);
lean_inc(x_1);
x_7 = l_Lean_Server_FileWorker_compileHeader(x_1, x_3, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 1);
x_13 = l_Lean_Server_FileWorker_CancelToken_new(x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_3);
lean_ctor_set(x_16, 2, x_4);
lean_ctor_set(x_16, 3, x_12);
x_17 = 1;
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_11);
lean_inc(x_1);
x_18 = l_Lean_Server_FileWorker_unfoldCmdSnaps(x_1, x_11, x_14, x_17, x_16, x_15);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_11);
lean_ctor_set(x_21, 2, x_20);
lean_ctor_set(x_21, 3, x_14);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_22);
lean_ctor_set(x_8, 1, x_23);
lean_ctor_set(x_8, 0, x_16);
lean_ctor_set(x_18, 0, x_8);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_11);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set(x_26, 3, x_14);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_8, 1, x_28);
lean_ctor_set(x_8, 0, x_16);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_8);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_16);
lean_dec(x_14);
lean_free_object(x_8);
lean_dec(x_11);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_18);
if (x_30 == 0)
{
return x_18;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_18, 0);
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_18);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_8, 0);
x_35 = lean_ctor_get(x_8, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_8);
x_36 = l_Lean_Server_FileWorker_CancelToken_new(x_9);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_2);
lean_ctor_set(x_39, 1, x_3);
lean_ctor_set(x_39, 2, x_4);
lean_ctor_set(x_39, 3, x_35);
x_40 = 1;
lean_inc(x_39);
lean_inc(x_37);
lean_inc(x_34);
lean_inc(x_1);
x_41 = l_Lean_Server_FileWorker_unfoldCmdSnaps(x_1, x_34, x_37, x_40, x_39, x_38);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_34);
lean_ctor_set(x_45, 2, x_42);
lean_ctor_set(x_45, 3, x_37);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_39);
lean_ctor_set(x_48, 1, x_47);
if (lean_is_scalar(x_44)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_44;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_1);
x_50 = lean_ctor_get(x_41, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_41, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_52 = x_41;
} else {
 lean_dec_ref(x_41);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_7);
if (x_54 == 0)
{
return x_7;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_7, 0);
x_56 = lean_ctor_get(x_7, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_7);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updatePendingRequests(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_apply_1(x_1, x_9);
lean_ctor_set(x_6, 1, x_10);
x_11 = lean_st_ref_set(x_3, x_6, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_21 = lean_apply_1(x_1, x_19);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_20);
x_23 = lean_st_ref_set(x_3, x_22, x_7);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_25 = x_23;
} else {
 lean_dec_ref(x_23);
 x_25 = lean_box(0);
}
x_26 = lean_box(0);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updatePendingRequests___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_updatePendingRequests(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_updateDocument___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Server_Snapshots_Snapshot_endPos(x_2);
x_4 = lean_nat_dec_lt(x_3, x_1);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = l_Lean_Server_FileWorker_CancelToken_new(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 0;
lean_inc(x_11);
lean_inc(x_1);
x_14 = l_Lean_Server_FileWorker_unfoldCmdSnaps(x_1, x_5, x_11, x_13, x_2, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_IO_AsyncList_ofList___rarg(x_4);
x_18 = l_IO_AsyncList_append___rarg(x_17, x_15);
x_19 = lean_st_ref_take(x_8, x_16);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set(x_22, 2, x_18);
lean_ctor_set(x_22, 3, x_11);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
lean_ctor_set(x_20, 0, x_22);
x_25 = lean_st_ref_set(x_8, x_20, x_21);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_20, 1);
x_33 = lean_ctor_get(x_20, 2);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_20);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_22);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_33);
x_35 = lean_st_ref_set(x_8, x_34, x_21);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
x_38 = lean_box(0);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_14);
if (x_40 == 0)
{
return x_14;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_14, 0);
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_14);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_updateDocument___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Internal server error: elab task was aborted while still in use.");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = l_IO_AsyncList_updateFinishedPrefix___rarg(x_10, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
x_17 = l_Lean_Server_FileWorker_CancelToken_set(x_16, x_14);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_ctor_get(x_19, 2);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_String_firstDiffPos(x_21, x_2);
lean_dec(x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_updateDocument___lambda__1___boxed), 2, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = l_IO_AsyncList_finishedPrefix___rarg(x_15);
lean_dec(x_15);
x_25 = l_List_takeWhile___rarg(x_23, x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_List_lengthTRAux___rarg(x_25, x_26);
x_28 = lean_nat_dec_eq(x_27, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_43; uint8_t x_44; 
x_29 = l_Lean_Server_Snapshots_instInhabitedSnapshot;
lean_inc(x_25);
x_30 = l_List_getLast_x21___rarg(x_29, x_25);
x_43 = lean_unsigned_to_nat(2u);
x_44 = lean_nat_dec_le(x_43, x_27);
if (x_44 == 0)
{
lean_dec(x_27);
lean_inc(x_5);
x_31 = x_5;
goto block_42;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_nat_sub(x_27, x_43);
lean_dec(x_27);
x_46 = l_List_get_x21___rarg(x_29, x_25, x_45);
x_31 = x_46;
goto block_42;
}
block_42:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_inc(x_31);
x_32 = l_Lean_Server_Snapshots_parseNextCmd(x_2, x_31, x_18);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
x_36 = l_Lean_Syntax_structEq(x_33, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_30);
x_37 = l_List_dropLast___rarg(x_25);
x_38 = lean_box(0);
x_39 = l_Lean_Server_FileWorker_updateDocument___lambda__2(x_3, x_4, x_5, x_37, x_31, x_38, x_7, x_8, x_34);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_31);
x_40 = lean_box(0);
x_41 = l_Lean_Server_FileWorker_updateDocument___lambda__2(x_3, x_4, x_5, x_25, x_30, x_40, x_7, x_8, x_34);
return x_41;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
x_47 = l_Lean_Server_FileWorker_CancelToken_new(x_18);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = 1;
lean_inc(x_48);
lean_inc(x_5);
lean_inc(x_3);
x_51 = l_Lean_Server_FileWorker_unfoldCmdSnaps(x_3, x_5, x_48, x_50, x_4, x_49);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_st_ref_take(x_8, x_53);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_57, 0, x_3);
lean_ctor_set(x_57, 1, x_5);
lean_ctor_set(x_57, 2, x_52);
lean_ctor_set(x_57, 3, x_48);
x_58 = !lean_is_exclusive(x_55);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_55, 0);
lean_dec(x_59);
lean_ctor_set(x_55, 0, x_57);
x_60 = lean_st_ref_set(x_8, x_55, x_56);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
x_63 = lean_box(0);
lean_ctor_set(x_60, 0, x_63);
return x_60;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
lean_dec(x_60);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_67 = lean_ctor_get(x_55, 1);
x_68 = lean_ctor_get(x_55, 2);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_55);
x_69 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_69, 0, x_57);
lean_ctor_set(x_69, 1, x_67);
lean_ctor_set(x_69, 2, x_68);
x_70 = lean_st_ref_set(x_8, x_69, x_56);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
x_73 = lean_box(0);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_dec(x_48);
lean_dec(x_5);
lean_dec(x_3);
x_75 = !lean_is_exclusive(x_51);
if (x_75 == 0)
{
return x_51;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_51, 0);
x_77 = lean_ctor_get(x_51, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_51);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
else
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_13, 0);
lean_inc(x_79);
lean_dec(x_13);
switch (lean_obj_tag(x_79)) {
case 0:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = lean_ctor_get(x_11, 1);
lean_inc(x_80);
lean_dec(x_11);
x_81 = l_Lean_Server_FileWorker_updateDocument___lambda__3___closed__1;
x_82 = l_IO_throwServerError___rarg(x_81, x_80);
return x_82;
}
case 1:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_83 = lean_ctor_get(x_11, 1);
lean_inc(x_83);
lean_dec(x_11);
x_84 = lean_ctor_get(x_12, 0);
lean_inc(x_84);
lean_dec(x_12);
x_85 = lean_ctor_get(x_1, 3);
lean_inc(x_85);
x_86 = l_Lean_Server_FileWorker_CancelToken_set(x_85, x_83);
lean_dec(x_85);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_ctor_get(x_1, 0);
lean_inc(x_88);
lean_dec(x_1);
x_89 = lean_ctor_get(x_88, 2);
lean_inc(x_89);
lean_dec(x_88);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec(x_89);
x_91 = l_String_firstDiffPos(x_90, x_2);
lean_dec(x_90);
x_92 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_updateDocument___lambda__1___boxed), 2, 1);
lean_closure_set(x_92, 0, x_91);
x_93 = l_IO_AsyncList_finishedPrefix___rarg(x_84);
lean_dec(x_84);
x_94 = l_List_takeWhile___rarg(x_92, x_93);
x_95 = lean_unsigned_to_nat(0u);
x_96 = l_List_lengthTRAux___rarg(x_94, x_95);
x_97 = lean_nat_dec_eq(x_96, x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_112; uint8_t x_113; 
x_98 = l_Lean_Server_Snapshots_instInhabitedSnapshot;
lean_inc(x_94);
x_99 = l_List_getLast_x21___rarg(x_98, x_94);
x_112 = lean_unsigned_to_nat(2u);
x_113 = lean_nat_dec_le(x_112, x_96);
if (x_113 == 0)
{
lean_dec(x_96);
lean_inc(x_5);
x_100 = x_5;
goto block_111;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_nat_sub(x_96, x_112);
lean_dec(x_96);
x_115 = l_List_get_x21___rarg(x_98, x_94, x_114);
x_100 = x_115;
goto block_111;
}
block_111:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
lean_inc(x_100);
x_101 = l_Lean_Server_Snapshots_parseNextCmd(x_2, x_100, x_87);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_ctor_get(x_99, 1);
lean_inc(x_104);
x_105 = l_Lean_Syntax_structEq(x_102, x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_99);
x_106 = l_List_dropLast___rarg(x_94);
x_107 = lean_box(0);
x_108 = l_Lean_Server_FileWorker_updateDocument___lambda__2(x_3, x_4, x_5, x_106, x_100, x_107, x_7, x_8, x_103);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_100);
x_109 = lean_box(0);
x_110 = l_Lean_Server_FileWorker_updateDocument___lambda__2(x_3, x_4, x_5, x_94, x_99, x_109, x_7, x_8, x_103);
return x_110;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; 
lean_dec(x_96);
lean_dec(x_94);
lean_dec(x_2);
x_116 = l_Lean_Server_FileWorker_CancelToken_new(x_87);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = 1;
lean_inc(x_117);
lean_inc(x_5);
lean_inc(x_3);
x_120 = l_Lean_Server_FileWorker_unfoldCmdSnaps(x_3, x_5, x_117, x_119, x_4, x_118);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_st_ref_take(x_8, x_122);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_126, 0, x_3);
lean_ctor_set(x_126, 1, x_5);
lean_ctor_set(x_126, 2, x_121);
lean_ctor_set(x_126, 3, x_117);
x_127 = !lean_is_exclusive(x_124);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_128 = lean_ctor_get(x_124, 0);
lean_dec(x_128);
lean_ctor_set(x_124, 0, x_126);
x_129 = lean_st_ref_set(x_8, x_124, x_125);
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_129, 0);
lean_dec(x_131);
x_132 = lean_box(0);
lean_ctor_set(x_129, 0, x_132);
return x_129;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_129, 1);
lean_inc(x_133);
lean_dec(x_129);
x_134 = lean_box(0);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_136 = lean_ctor_get(x_124, 1);
x_137 = lean_ctor_get(x_124, 2);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_124);
x_138 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_138, 0, x_126);
lean_ctor_set(x_138, 1, x_136);
lean_ctor_set(x_138, 2, x_137);
x_139 = lean_st_ref_set(x_8, x_138, x_125);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_141 = x_139;
} else {
 lean_dec_ref(x_139);
 x_141 = lean_box(0);
}
x_142 = lean_box(0);
if (lean_is_scalar(x_141)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_141;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_140);
return x_143;
}
}
else
{
uint8_t x_144; 
lean_dec(x_117);
lean_dec(x_5);
lean_dec(x_3);
x_144 = !lean_is_exclusive(x_120);
if (x_144 == 0)
{
return x_120;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_120, 0);
x_146 = lean_ctor_get(x_120, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_120);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
}
default: 
{
uint8_t x_148; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_148 = !lean_is_exclusive(x_11);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_11, 0);
lean_dec(x_149);
x_150 = lean_ctor_get(x_79, 0);
lean_inc(x_150);
lean_dec(x_79);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_150);
return x_11;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_11, 1);
lean_inc(x_151);
lean_dec(x_11);
x_152 = lean_ctor_get(x_79, 0);
lean_inc(x_152);
lean_dec(x_79);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_updateDocument___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Internal server error: header changed but worker wasn't restarted.");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
x_12 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
x_13 = l_Lean_Server_Snapshots_reparseHeader(x_10, x_11, x_12, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = l_Lean_Syntax_structEq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = l_Lean_Server_FileWorker_updateDocument___closed__1;
x_20 = l_IO_throwServerError___rarg(x_19, x_15);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
lean_inc(x_2);
x_26 = l_Lean_Server_FileWorker_updateDocument___lambda__3(x_8, x_10, x_1, x_2, x_14, x_25, x_2, x_3, x_15);
lean_dec(x_3);
lean_dec(x_2);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_13);
if (x_27 == 0)
{
return x_13;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_13, 0);
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_13);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Server_FileWorker_updateDocument___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Server_FileWorker_updateDocument___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Server_FileWorker_updateDocument___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_10;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleDidChange___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Expected version number");
return x_1;
}
}
static uint8_t _init_l_Lean_Server_FileWorker_handleDidChange___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 0;
x_2 = l_instDecidableNot___rarg(x_1);
return x_2;
}
}
static uint8_t _init_l_Lean_Server_FileWorker_handleDidChange___closed__3() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 1;
x_2 = l_instDecidableNot___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleDidChange___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Got outdated version number: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleDidChange___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" ≤ ");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDidChange(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_st_ref_get(x_3, x_4);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Server_FileWorker_handleDidChange___closed__1;
x_11 = l_IO_throwServerError___rarg(x_10, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_nat_dec_le(x_16, x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_19);
x_21 = l_Array_isEmpty___rarg(x_6);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Server_FileWorker_handleDidChange___closed__2;
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_box(0);
lean_ctor_set(x_7, 0, x_23);
return x_7;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_free_object(x_7);
x_24 = lean_ctor_get(x_18, 2);
lean_inc(x_24);
lean_dec(x_18);
x_25 = l_Lean_Server_foldDocumentChanges(x_6, x_24);
lean_dec(x_6);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 2, x_25);
x_27 = l_Lean_Server_FileWorker_updateDocument(x_26, x_2, x_3, x_14);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = l_Lean_Server_FileWorker_handleDidChange___closed__3;
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_box(0);
lean_ctor_set(x_7, 0, x_29);
return x_7;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_free_object(x_7);
x_30 = lean_ctor_get(x_18, 2);
lean_inc(x_30);
lean_dec(x_18);
x_31 = l_Lean_Server_foldDocumentChanges(x_6, x_30);
lean_dec(x_6);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_15);
lean_ctor_set(x_32, 1, x_16);
lean_ctor_set(x_32, 2, x_31);
x_33 = l_Lean_Server_FileWorker_updateDocument(x_32, x_2, x_3, x_14);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_18);
lean_dec(x_15);
lean_free_object(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_34 = l_Nat_repr(x_16);
x_35 = l_Lean_Server_FileWorker_handleDidChange___closed__4;
x_36 = lean_string_append(x_35, x_34);
lean_dec(x_34);
x_37 = l_Lean_Server_FileWorker_handleDidChange___closed__5;
x_38 = lean_string_append(x_36, x_37);
x_39 = l_Nat_repr(x_19);
x_40 = lean_string_append(x_38, x_39);
lean_dec(x_39);
x_41 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_42 = lean_string_append(x_40, x_41);
x_43 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_42, x_14);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_44 = lean_ctor_get(x_7, 0);
x_45 = lean_ctor_get(x_7, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_7);
x_46 = lean_ctor_get(x_5, 0);
lean_inc(x_46);
lean_dec(x_5);
x_47 = lean_ctor_get(x_8, 0);
lean_inc(x_47);
lean_dec(x_8);
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
x_51 = lean_nat_dec_le(x_47, x_50);
if (x_51 == 0)
{
uint8_t x_52; 
lean_dec(x_50);
x_52 = l_Array_isEmpty___rarg(x_6);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = l_Lean_Server_FileWorker_handleDidChange___closed__2;
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_45);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_49, 2);
lean_inc(x_56);
lean_dec(x_49);
x_57 = l_Lean_Server_foldDocumentChanges(x_6, x_56);
lean_dec(x_6);
x_58 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_58, 0, x_46);
lean_ctor_set(x_58, 1, x_47);
lean_ctor_set(x_58, 2, x_57);
x_59 = l_Lean_Server_FileWorker_updateDocument(x_58, x_2, x_3, x_45);
return x_59;
}
}
else
{
uint8_t x_60; 
x_60 = l_Lean_Server_FileWorker_handleDidChange___closed__3;
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_45);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_49, 2);
lean_inc(x_63);
lean_dec(x_49);
x_64 = l_Lean_Server_foldDocumentChanges(x_6, x_63);
lean_dec(x_6);
x_65 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_65, 0, x_46);
lean_ctor_set(x_65, 1, x_47);
lean_ctor_set(x_65, 2, x_64);
x_66 = l_Lean_Server_FileWorker_updateDocument(x_65, x_2, x_3, x_45);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_49);
lean_dec(x_46);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_67 = l_Nat_repr(x_47);
x_68 = l_Lean_Server_FileWorker_handleDidChange___closed__4;
x_69 = lean_string_append(x_68, x_67);
lean_dec(x_67);
x_70 = l_Lean_Server_FileWorker_handleDidChange___closed__5;
x_71 = lean_string_append(x_69, x_70);
x_72 = l_Nat_repr(x_50);
x_73 = lean_string_append(x_71, x_72);
lean_dec(x_72);
x_74 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_75 = lean_string_append(x_73, x_74);
x_76 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_75, x_45);
return x_76;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_del___at_Lean_Server_FileWorker_handleCancelRequest___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
lean_inc(x_1);
x_9 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_118_(x_1, x_6);
switch (x_9) {
case 0:
{
uint8_t x_10; 
x_10 = l_Std_RBNode_isBlack___rarg(x_5);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Std_RBNode_del___at_Lean_Server_FileWorker_handleCancelRequest___spec__2(x_1, x_5);
x_12 = 0;
lean_ctor_set(x_2, 0, x_11);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_12);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_free_object(x_2);
x_13 = l_Std_RBNode_del___at_Lean_Server_FileWorker_handleCancelRequest___spec__2(x_1, x_5);
x_14 = l_Std_RBNode_balLeft___rarg(x_13, x_6, x_7, x_8);
return x_14;
}
}
case 1:
{
lean_object* x_15; 
lean_free_object(x_2);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_15 = l_Std_RBNode_appendTrees___rarg(x_5, x_8);
return x_15;
}
default: 
{
uint8_t x_16; 
x_16 = l_Std_RBNode_isBlack___rarg(x_8);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Std_RBNode_del___at_Lean_Server_FileWorker_handleCancelRequest___spec__2(x_1, x_8);
x_18 = 0;
lean_ctor_set(x_2, 3, x_17);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_18);
return x_2;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_2);
x_19 = l_Std_RBNode_del___at_Lean_Server_FileWorker_handleCancelRequest___spec__2(x_1, x_8);
x_20 = l_Std_RBNode_balRight___rarg(x_5, x_6, x_7, x_19);
return x_20;
}
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_2, 3);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
lean_inc(x_22);
lean_inc(x_1);
x_25 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_118_(x_1, x_22);
switch (x_25) {
case 0:
{
uint8_t x_26; 
x_26 = l_Std_RBNode_isBlack___rarg(x_21);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = l_Std_RBNode_del___at_Lean_Server_FileWorker_handleCancelRequest___spec__2(x_1, x_21);
x_28 = 0;
x_29 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_22);
lean_ctor_set(x_29, 2, x_23);
lean_ctor_set(x_29, 3, x_24);
lean_ctor_set_uint8(x_29, sizeof(void*)*4, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Std_RBNode_del___at_Lean_Server_FileWorker_handleCancelRequest___spec__2(x_1, x_21);
x_31 = l_Std_RBNode_balLeft___rarg(x_30, x_22, x_23, x_24);
return x_31;
}
}
case 1:
{
lean_object* x_32; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
x_32 = l_Std_RBNode_appendTrees___rarg(x_21, x_24);
return x_32;
}
default: 
{
uint8_t x_33; 
x_33 = l_Std_RBNode_isBlack___rarg(x_24);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = l_Std_RBNode_del___at_Lean_Server_FileWorker_handleCancelRequest___spec__2(x_1, x_24);
x_35 = 0;
x_36 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_36, 0, x_21);
lean_ctor_set(x_36, 1, x_22);
lean_ctor_set(x_36, 2, x_23);
lean_ctor_set(x_36, 3, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Std_RBNode_del___at_Lean_Server_FileWorker_handleCancelRequest___spec__2(x_1, x_24);
x_38 = l_Std_RBNode_balRight___rarg(x_21, x_22, x_23, x_37);
return x_38;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_erase___at_Lean_Server_FileWorker_handleCancelRequest___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Std_RBNode_del___at_Lean_Server_FileWorker_handleCancelRequest___spec__2(x_1, x_2);
x_4 = l_Std_RBNode_setBlack___rarg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCancelRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Std_RBNode_erase___at_Lean_Server_FileWorker_handleCancelRequest___spec__1), 2, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Lean_Server_FileWorker_updatePendingRequests(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCancelRequest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_handleCancelRequest(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_FileWorker_handleRpcRelease___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_10 = lean_array_uget(x_1, x_3);
x_11 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_12 = l_Lean_Server_FileWorker_RpcSession_release(x_4, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
x_4 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcRelease(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 2);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_11 = l_Std_RBNode_find___at_Lean_Server_registerRpcCallHandler___spec__1(x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_box(0);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_free_object(x_5);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_13, x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_array_get_size(x_17);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = 0;
x_21 = l_Array_forInUnsafe_loop___at_Lean_Server_FileWorker_handleRpcRelease___spec__1(x_17, x_19, x_20, x_15, x_2, x_3, x_16);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Server_FileWorker_RpcSession_keptAlive(x_22, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_st_ref_set(x_13, x_25, x_26);
lean_dec(x_13);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint64_t x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_5, 0);
x_33 = lean_ctor_get(x_5, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_5);
x_34 = lean_ctor_get(x_32, 2);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_36 = l_Std_RBNode_find___at_Lean_Server_registerRpcCallHandler___spec__1(x_34, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_st_ref_get(x_39, x_33);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_1, 1);
x_44 = lean_array_get_size(x_43);
x_45 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_46 = 0;
x_47 = l_Array_forInUnsafe_loop___at_Lean_Server_FileWorker_handleRpcRelease___spec__1(x_43, x_45, x_46, x_41, x_2, x_3, x_42);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_Server_FileWorker_RpcSession_keptAlive(x_48, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_st_ref_set(x_39, x_51, x_52);
lean_dec(x_39);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_FileWorker_handleRpcRelease___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forInUnsafe_loop___at_Lean_Server_FileWorker_handleRpcRelease___spec__1(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcRelease___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_handleRpcRelease(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcKeepAlive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 2);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_11 = l_Std_RBNode_find___at_Lean_Server_registerRpcCallHandler___spec__1(x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_box(0);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_free_object(x_5);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_13, x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Server_FileWorker_RpcSession_keptAlive(x_15, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_set(x_13, x_18, x_19);
lean_dec(x_13);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_5, 0);
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_5);
x_27 = lean_ctor_get(x_25, 2);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_29 = l_Std_RBNode_find___at_Lean_Server_registerRpcCallHandler___spec__1(x_27, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_st_ref_get(x_32, x_26);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Server_FileWorker_RpcSession_keptAlive(x_34, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_st_ref_set(x_32, x_37, x_38);
lean_dec(x_32);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcKeepAlive___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_handleRpcKeepAlive(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = 0;
x_6 = lean_box_uint64(x_2);
x_7 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set_uint8(x_7, sizeof(void*)*4, x_5);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_1, 3);
x_14 = lean_unbox_uint64(x_11);
x_15 = lean_uint64_dec_lt(x_2, x_14);
if (x_15 == 0)
{
uint64_t x_16; uint8_t x_17; 
x_16 = lean_unbox_uint64(x_11);
x_17 = lean_uint64_dec_eq(x_2, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Std_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2(x_13, x_2, x_3);
x_19 = 0;
lean_ctor_set(x_1, 3, x_18);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_19);
return x_1;
}
else
{
uint8_t x_20; lean_object* x_21; 
lean_dec(x_12);
lean_dec(x_11);
x_20 = 0;
x_21 = lean_box_uint64(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_21);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_20);
return x_1;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Std_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2(x_10, x_2, x_3);
x_23 = 0;
lean_ctor_set(x_1, 0, x_22);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_23);
return x_1;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 1);
x_26 = lean_ctor_get(x_1, 2);
x_27 = lean_ctor_get(x_1, 3);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_1);
x_28 = lean_unbox_uint64(x_25);
x_29 = lean_uint64_dec_lt(x_2, x_28);
if (x_29 == 0)
{
uint64_t x_30; uint8_t x_31; 
x_30 = lean_unbox_uint64(x_25);
x_31 = lean_uint64_dec_eq(x_2, x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_32 = l_Std_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2(x_27, x_2, x_3);
x_33 = 0;
x_34 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_25);
lean_ctor_set(x_34, 2, x_26);
lean_ctor_set(x_34, 3, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*4, x_33);
return x_34;
}
else
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_26);
lean_dec(x_25);
x_35 = 0;
x_36 = lean_box_uint64(x_2);
x_37 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_37, 0, x_24);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_3);
lean_ctor_set(x_37, 3, x_27);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_35);
return x_37;
}
}
else
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_38 = l_Std_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2(x_24, x_2, x_3);
x_39 = 0;
x_40 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_25);
lean_ctor_set(x_40, 2, x_26);
lean_ctor_set(x_40, 3, x_27);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_1);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; uint8_t x_47; 
x_42 = lean_ctor_get(x_1, 0);
x_43 = lean_ctor_get(x_1, 1);
x_44 = lean_ctor_get(x_1, 2);
x_45 = lean_ctor_get(x_1, 3);
x_46 = lean_unbox_uint64(x_43);
x_47 = lean_uint64_dec_lt(x_2, x_46);
if (x_47 == 0)
{
uint64_t x_48; uint8_t x_49; 
x_48 = lean_unbox_uint64(x_43);
x_49 = lean_uint64_dec_eq(x_2, x_48);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = l_Std_RBNode_isRed___rarg(x_45);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = l_Std_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2(x_45, x_2, x_3);
x_52 = 1;
lean_ctor_set(x_1, 3, x_51);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_52);
return x_1;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = l_Std_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2(x_45, x_2, x_3);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 3);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_53);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_53, 3);
lean_dec(x_57);
x_58 = lean_ctor_get(x_53, 0);
lean_dec(x_58);
x_59 = 0;
lean_ctor_set(x_53, 0, x_55);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_59);
x_60 = 1;
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_60);
return x_1;
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_53, 1);
x_62 = lean_ctor_get(x_53, 2);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_53);
x_63 = 0;
x_64 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_64, 0, x_55);
lean_ctor_set(x_64, 1, x_61);
lean_ctor_set(x_64, 2, x_62);
lean_ctor_set(x_64, 3, x_55);
lean_ctor_set_uint8(x_64, sizeof(void*)*4, x_63);
x_65 = 1;
lean_ctor_set(x_1, 3, x_64);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_65);
return x_1;
}
}
else
{
uint8_t x_66; 
x_66 = lean_ctor_get_uint8(x_55, sizeof(void*)*4);
if (x_66 == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_53);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_68 = lean_ctor_get(x_53, 1);
x_69 = lean_ctor_get(x_53, 2);
x_70 = lean_ctor_get(x_53, 3);
lean_dec(x_70);
x_71 = lean_ctor_get(x_53, 0);
lean_dec(x_71);
x_72 = !lean_is_exclusive(x_55);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_78; 
x_73 = lean_ctor_get(x_55, 0);
x_74 = lean_ctor_get(x_55, 1);
x_75 = lean_ctor_get(x_55, 2);
x_76 = lean_ctor_get(x_55, 3);
x_77 = 1;
lean_ctor_set(x_55, 3, x_54);
lean_ctor_set(x_55, 2, x_44);
lean_ctor_set(x_55, 1, x_43);
lean_ctor_set(x_55, 0, x_42);
lean_ctor_set_uint8(x_55, sizeof(void*)*4, x_77);
lean_ctor_set(x_53, 3, x_76);
lean_ctor_set(x_53, 2, x_75);
lean_ctor_set(x_53, 1, x_74);
lean_ctor_set(x_53, 0, x_73);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_77);
x_78 = 0;
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set(x_1, 2, x_69);
lean_ctor_set(x_1, 1, x_68);
lean_ctor_set(x_1, 0, x_55);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_78);
return x_1;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; uint8_t x_85; 
x_79 = lean_ctor_get(x_55, 0);
x_80 = lean_ctor_get(x_55, 1);
x_81 = lean_ctor_get(x_55, 2);
x_82 = lean_ctor_get(x_55, 3);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_55);
x_83 = 1;
x_84 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_84, 0, x_42);
lean_ctor_set(x_84, 1, x_43);
lean_ctor_set(x_84, 2, x_44);
lean_ctor_set(x_84, 3, x_54);
lean_ctor_set_uint8(x_84, sizeof(void*)*4, x_83);
lean_ctor_set(x_53, 3, x_82);
lean_ctor_set(x_53, 2, x_81);
lean_ctor_set(x_53, 1, x_80);
lean_ctor_set(x_53, 0, x_79);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_83);
x_85 = 0;
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set(x_1, 2, x_69);
lean_ctor_set(x_1, 1, x_68);
lean_ctor_set(x_1, 0, x_84);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_86 = lean_ctor_get(x_53, 1);
x_87 = lean_ctor_get(x_53, 2);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_53);
x_88 = lean_ctor_get(x_55, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_55, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_55, 2);
lean_inc(x_90);
x_91 = lean_ctor_get(x_55, 3);
lean_inc(x_91);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 lean_ctor_release(x_55, 3);
 x_92 = x_55;
} else {
 lean_dec_ref(x_55);
 x_92 = lean_box(0);
}
x_93 = 1;
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(1, 4, 1);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_42);
lean_ctor_set(x_94, 1, x_43);
lean_ctor_set(x_94, 2, x_44);
lean_ctor_set(x_94, 3, x_54);
lean_ctor_set_uint8(x_94, sizeof(void*)*4, x_93);
x_95 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_95, 0, x_88);
lean_ctor_set(x_95, 1, x_89);
lean_ctor_set(x_95, 2, x_90);
lean_ctor_set(x_95, 3, x_91);
lean_ctor_set_uint8(x_95, sizeof(void*)*4, x_93);
x_96 = 0;
lean_ctor_set(x_1, 3, x_95);
lean_ctor_set(x_1, 2, x_87);
lean_ctor_set(x_1, 1, x_86);
lean_ctor_set(x_1, 0, x_94);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_96);
return x_1;
}
}
else
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_53);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_101; 
x_98 = lean_ctor_get(x_53, 3);
lean_dec(x_98);
x_99 = lean_ctor_get(x_53, 0);
lean_dec(x_99);
x_100 = 0;
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_100);
x_101 = 1;
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_101);
return x_1;
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; uint8_t x_106; 
x_102 = lean_ctor_get(x_53, 1);
x_103 = lean_ctor_get(x_53, 2);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_53);
x_104 = 0;
x_105 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_105, 0, x_54);
lean_ctor_set(x_105, 1, x_102);
lean_ctor_set(x_105, 2, x_103);
lean_ctor_set(x_105, 3, x_55);
lean_ctor_set_uint8(x_105, sizeof(void*)*4, x_104);
x_106 = 1;
lean_ctor_set(x_1, 3, x_105);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_106);
return x_1;
}
}
}
}
else
{
uint8_t x_107; 
x_107 = lean_ctor_get_uint8(x_54, sizeof(void*)*4);
if (x_107 == 0)
{
uint8_t x_108; 
x_108 = !lean_is_exclusive(x_53);
if (x_108 == 0)
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_ctor_get(x_53, 0);
lean_dec(x_109);
x_110 = !lean_is_exclusive(x_54);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; uint8_t x_116; 
x_111 = lean_ctor_get(x_54, 0);
x_112 = lean_ctor_get(x_54, 1);
x_113 = lean_ctor_get(x_54, 2);
x_114 = lean_ctor_get(x_54, 3);
x_115 = 1;
lean_ctor_set(x_54, 3, x_111);
lean_ctor_set(x_54, 2, x_44);
lean_ctor_set(x_54, 1, x_43);
lean_ctor_set(x_54, 0, x_42);
lean_ctor_set_uint8(x_54, sizeof(void*)*4, x_115);
lean_ctor_set(x_53, 0, x_114);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_115);
x_116 = 0;
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set(x_1, 2, x_113);
lean_ctor_set(x_1, 1, x_112);
lean_ctor_set(x_1, 0, x_54);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_116);
return x_1;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; uint8_t x_123; 
x_117 = lean_ctor_get(x_54, 0);
x_118 = lean_ctor_get(x_54, 1);
x_119 = lean_ctor_get(x_54, 2);
x_120 = lean_ctor_get(x_54, 3);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_54);
x_121 = 1;
x_122 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_122, 0, x_42);
lean_ctor_set(x_122, 1, x_43);
lean_ctor_set(x_122, 2, x_44);
lean_ctor_set(x_122, 3, x_117);
lean_ctor_set_uint8(x_122, sizeof(void*)*4, x_121);
lean_ctor_set(x_53, 0, x_120);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_121);
x_123 = 0;
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set(x_1, 2, x_119);
lean_ctor_set(x_1, 1, x_118);
lean_ctor_set(x_1, 0, x_122);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_123);
return x_1;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_124 = lean_ctor_get(x_53, 1);
x_125 = lean_ctor_get(x_53, 2);
x_126 = lean_ctor_get(x_53, 3);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_53);
x_127 = lean_ctor_get(x_54, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_54, 1);
lean_inc(x_128);
x_129 = lean_ctor_get(x_54, 2);
lean_inc(x_129);
x_130 = lean_ctor_get(x_54, 3);
lean_inc(x_130);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 x_131 = x_54;
} else {
 lean_dec_ref(x_54);
 x_131 = lean_box(0);
}
x_132 = 1;
if (lean_is_scalar(x_131)) {
 x_133 = lean_alloc_ctor(1, 4, 1);
} else {
 x_133 = x_131;
}
lean_ctor_set(x_133, 0, x_42);
lean_ctor_set(x_133, 1, x_43);
lean_ctor_set(x_133, 2, x_44);
lean_ctor_set(x_133, 3, x_127);
lean_ctor_set_uint8(x_133, sizeof(void*)*4, x_132);
x_134 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_134, 0, x_130);
lean_ctor_set(x_134, 1, x_124);
lean_ctor_set(x_134, 2, x_125);
lean_ctor_set(x_134, 3, x_126);
lean_ctor_set_uint8(x_134, sizeof(void*)*4, x_132);
x_135 = 0;
lean_ctor_set(x_1, 3, x_134);
lean_ctor_set(x_1, 2, x_129);
lean_ctor_set(x_1, 1, x_128);
lean_ctor_set(x_1, 0, x_133);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_135);
return x_1;
}
}
else
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_53, 3);
lean_inc(x_136);
if (lean_obj_tag(x_136) == 0)
{
uint8_t x_137; 
x_137 = !lean_is_exclusive(x_53);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; uint8_t x_141; 
x_138 = lean_ctor_get(x_53, 3);
lean_dec(x_138);
x_139 = lean_ctor_get(x_53, 0);
lean_dec(x_139);
x_140 = 0;
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_140);
x_141 = 1;
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_141);
return x_1;
}
else
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; uint8_t x_146; 
x_142 = lean_ctor_get(x_53, 1);
x_143 = lean_ctor_get(x_53, 2);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_53);
x_144 = 0;
x_145 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_145, 0, x_54);
lean_ctor_set(x_145, 1, x_142);
lean_ctor_set(x_145, 2, x_143);
lean_ctor_set(x_145, 3, x_136);
lean_ctor_set_uint8(x_145, sizeof(void*)*4, x_144);
x_146 = 1;
lean_ctor_set(x_1, 3, x_145);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_146);
return x_1;
}
}
else
{
uint8_t x_147; 
x_147 = lean_ctor_get_uint8(x_136, sizeof(void*)*4);
if (x_147 == 0)
{
uint8_t x_148; 
lean_free_object(x_1);
x_148 = !lean_is_exclusive(x_53);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_149 = lean_ctor_get(x_53, 3);
lean_dec(x_149);
x_150 = lean_ctor_get(x_53, 0);
lean_dec(x_150);
x_151 = !lean_is_exclusive(x_136);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; uint8_t x_157; 
x_152 = lean_ctor_get(x_136, 0);
x_153 = lean_ctor_get(x_136, 1);
x_154 = lean_ctor_get(x_136, 2);
x_155 = lean_ctor_get(x_136, 3);
x_156 = 1;
lean_inc(x_54);
lean_ctor_set(x_136, 3, x_54);
lean_ctor_set(x_136, 2, x_44);
lean_ctor_set(x_136, 1, x_43);
lean_ctor_set(x_136, 0, x_42);
x_157 = !lean_is_exclusive(x_54);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_158 = lean_ctor_get(x_54, 3);
lean_dec(x_158);
x_159 = lean_ctor_get(x_54, 2);
lean_dec(x_159);
x_160 = lean_ctor_get(x_54, 1);
lean_dec(x_160);
x_161 = lean_ctor_get(x_54, 0);
lean_dec(x_161);
lean_ctor_set_uint8(x_136, sizeof(void*)*4, x_156);
lean_ctor_set(x_54, 3, x_155);
lean_ctor_set(x_54, 2, x_154);
lean_ctor_set(x_54, 1, x_153);
lean_ctor_set(x_54, 0, x_152);
lean_ctor_set_uint8(x_54, sizeof(void*)*4, x_156);
x_162 = 0;
lean_ctor_set(x_53, 3, x_54);
lean_ctor_set(x_53, 0, x_136);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_162);
return x_53;
}
else
{
lean_object* x_163; uint8_t x_164; 
lean_dec(x_54);
lean_ctor_set_uint8(x_136, sizeof(void*)*4, x_156);
x_163 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_163, 0, x_152);
lean_ctor_set(x_163, 1, x_153);
lean_ctor_set(x_163, 2, x_154);
lean_ctor_set(x_163, 3, x_155);
lean_ctor_set_uint8(x_163, sizeof(void*)*4, x_156);
x_164 = 0;
lean_ctor_set(x_53, 3, x_163);
lean_ctor_set(x_53, 0, x_136);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_164);
return x_53;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_165 = lean_ctor_get(x_136, 0);
x_166 = lean_ctor_get(x_136, 1);
x_167 = lean_ctor_get(x_136, 2);
x_168 = lean_ctor_get(x_136, 3);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_136);
x_169 = 1;
lean_inc(x_54);
x_170 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_170, 0, x_42);
lean_ctor_set(x_170, 1, x_43);
lean_ctor_set(x_170, 2, x_44);
lean_ctor_set(x_170, 3, x_54);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 x_171 = x_54;
} else {
 lean_dec_ref(x_54);
 x_171 = lean_box(0);
}
lean_ctor_set_uint8(x_170, sizeof(void*)*4, x_169);
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 4, 1);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_165);
lean_ctor_set(x_172, 1, x_166);
lean_ctor_set(x_172, 2, x_167);
lean_ctor_set(x_172, 3, x_168);
lean_ctor_set_uint8(x_172, sizeof(void*)*4, x_169);
x_173 = 0;
lean_ctor_set(x_53, 3, x_172);
lean_ctor_set(x_53, 0, x_170);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_173);
return x_53;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; 
x_174 = lean_ctor_get(x_53, 1);
x_175 = lean_ctor_get(x_53, 2);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_53);
x_176 = lean_ctor_get(x_136, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_136, 1);
lean_inc(x_177);
x_178 = lean_ctor_get(x_136, 2);
lean_inc(x_178);
x_179 = lean_ctor_get(x_136, 3);
lean_inc(x_179);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 lean_ctor_release(x_136, 2);
 lean_ctor_release(x_136, 3);
 x_180 = x_136;
} else {
 lean_dec_ref(x_136);
 x_180 = lean_box(0);
}
x_181 = 1;
lean_inc(x_54);
if (lean_is_scalar(x_180)) {
 x_182 = lean_alloc_ctor(1, 4, 1);
} else {
 x_182 = x_180;
}
lean_ctor_set(x_182, 0, x_42);
lean_ctor_set(x_182, 1, x_43);
lean_ctor_set(x_182, 2, x_44);
lean_ctor_set(x_182, 3, x_54);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 x_183 = x_54;
} else {
 lean_dec_ref(x_54);
 x_183 = lean_box(0);
}
lean_ctor_set_uint8(x_182, sizeof(void*)*4, x_181);
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 4, 1);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_176);
lean_ctor_set(x_184, 1, x_177);
lean_ctor_set(x_184, 2, x_178);
lean_ctor_set(x_184, 3, x_179);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_181);
x_185 = 0;
x_186 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_186, 0, x_182);
lean_ctor_set(x_186, 1, x_174);
lean_ctor_set(x_186, 2, x_175);
lean_ctor_set(x_186, 3, x_184);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_185);
return x_186;
}
}
else
{
uint8_t x_187; 
x_187 = !lean_is_exclusive(x_53);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_188 = lean_ctor_get(x_53, 3);
lean_dec(x_188);
x_189 = lean_ctor_get(x_53, 0);
lean_dec(x_189);
x_190 = !lean_is_exclusive(x_54);
if (x_190 == 0)
{
uint8_t x_191; uint8_t x_192; 
lean_ctor_set_uint8(x_54, sizeof(void*)*4, x_147);
x_191 = 0;
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_191);
x_192 = 1;
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_192);
return x_1;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; uint8_t x_199; 
x_193 = lean_ctor_get(x_54, 0);
x_194 = lean_ctor_get(x_54, 1);
x_195 = lean_ctor_get(x_54, 2);
x_196 = lean_ctor_get(x_54, 3);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_54);
x_197 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_197, 0, x_193);
lean_ctor_set(x_197, 1, x_194);
lean_ctor_set(x_197, 2, x_195);
lean_ctor_set(x_197, 3, x_196);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_147);
x_198 = 0;
lean_ctor_set(x_53, 0, x_197);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_198);
x_199 = 1;
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; lean_object* x_209; uint8_t x_210; 
x_200 = lean_ctor_get(x_53, 1);
x_201 = lean_ctor_get(x_53, 2);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_53);
x_202 = lean_ctor_get(x_54, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_54, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_54, 2);
lean_inc(x_204);
x_205 = lean_ctor_get(x_54, 3);
lean_inc(x_205);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 x_206 = x_54;
} else {
 lean_dec_ref(x_54);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 4, 1);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_202);
lean_ctor_set(x_207, 1, x_203);
lean_ctor_set(x_207, 2, x_204);
lean_ctor_set(x_207, 3, x_205);
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_147);
x_208 = 0;
x_209 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_200);
lean_ctor_set(x_209, 2, x_201);
lean_ctor_set(x_209, 3, x_136);
lean_ctor_set_uint8(x_209, sizeof(void*)*4, x_208);
x_210 = 1;
lean_ctor_set(x_1, 3, x_209);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_210);
return x_1;
}
}
}
}
}
}
}
else
{
uint8_t x_211; lean_object* x_212; 
lean_dec(x_44);
lean_dec(x_43);
x_211 = 1;
x_212 = lean_box_uint64(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_212);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_211);
return x_1;
}
}
else
{
uint8_t x_213; 
x_213 = l_Std_RBNode_isRed___rarg(x_42);
if (x_213 == 0)
{
lean_object* x_214; uint8_t x_215; 
x_214 = l_Std_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2(x_42, x_2, x_3);
x_215 = 1;
lean_ctor_set(x_1, 0, x_214);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_215);
return x_1;
}
else
{
lean_object* x_216; lean_object* x_217; 
x_216 = l_Std_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2(x_42, x_2, x_3);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; 
x_218 = lean_ctor_get(x_216, 3);
lean_inc(x_218);
if (lean_obj_tag(x_218) == 0)
{
uint8_t x_219; 
x_219 = !lean_is_exclusive(x_216);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; uint8_t x_222; uint8_t x_223; 
x_220 = lean_ctor_get(x_216, 3);
lean_dec(x_220);
x_221 = lean_ctor_get(x_216, 0);
lean_dec(x_221);
x_222 = 0;
lean_ctor_set(x_216, 0, x_218);
lean_ctor_set_uint8(x_216, sizeof(void*)*4, x_222);
x_223 = 1;
lean_ctor_set(x_1, 0, x_216);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_223);
return x_1;
}
else
{
lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; uint8_t x_228; 
x_224 = lean_ctor_get(x_216, 1);
x_225 = lean_ctor_get(x_216, 2);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_216);
x_226 = 0;
x_227 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_227, 0, x_218);
lean_ctor_set(x_227, 1, x_224);
lean_ctor_set(x_227, 2, x_225);
lean_ctor_set(x_227, 3, x_218);
lean_ctor_set_uint8(x_227, sizeof(void*)*4, x_226);
x_228 = 1;
lean_ctor_set(x_1, 0, x_227);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_228);
return x_1;
}
}
else
{
uint8_t x_229; 
x_229 = lean_ctor_get_uint8(x_218, sizeof(void*)*4);
if (x_229 == 0)
{
uint8_t x_230; 
x_230 = !lean_is_exclusive(x_216);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; 
x_231 = lean_ctor_get(x_216, 1);
x_232 = lean_ctor_get(x_216, 2);
x_233 = lean_ctor_get(x_216, 3);
lean_dec(x_233);
x_234 = lean_ctor_get(x_216, 0);
lean_dec(x_234);
x_235 = !lean_is_exclusive(x_218);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; uint8_t x_241; 
x_236 = lean_ctor_get(x_218, 0);
x_237 = lean_ctor_get(x_218, 1);
x_238 = lean_ctor_get(x_218, 2);
x_239 = lean_ctor_get(x_218, 3);
x_240 = 1;
lean_ctor_set(x_218, 3, x_236);
lean_ctor_set(x_218, 2, x_232);
lean_ctor_set(x_218, 1, x_231);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set_uint8(x_218, sizeof(void*)*4, x_240);
lean_ctor_set(x_216, 3, x_45);
lean_ctor_set(x_216, 2, x_44);
lean_ctor_set(x_216, 1, x_43);
lean_ctor_set(x_216, 0, x_239);
lean_ctor_set_uint8(x_216, sizeof(void*)*4, x_240);
x_241 = 0;
lean_ctor_set(x_1, 3, x_216);
lean_ctor_set(x_1, 2, x_238);
lean_ctor_set(x_1, 1, x_237);
lean_ctor_set(x_1, 0, x_218);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_241);
return x_1;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; uint8_t x_248; 
x_242 = lean_ctor_get(x_218, 0);
x_243 = lean_ctor_get(x_218, 1);
x_244 = lean_ctor_get(x_218, 2);
x_245 = lean_ctor_get(x_218, 3);
lean_inc(x_245);
lean_inc(x_244);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_218);
x_246 = 1;
x_247 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_247, 0, x_217);
lean_ctor_set(x_247, 1, x_231);
lean_ctor_set(x_247, 2, x_232);
lean_ctor_set(x_247, 3, x_242);
lean_ctor_set_uint8(x_247, sizeof(void*)*4, x_246);
lean_ctor_set(x_216, 3, x_45);
lean_ctor_set(x_216, 2, x_44);
lean_ctor_set(x_216, 1, x_43);
lean_ctor_set(x_216, 0, x_245);
lean_ctor_set_uint8(x_216, sizeof(void*)*4, x_246);
x_248 = 0;
lean_ctor_set(x_1, 3, x_216);
lean_ctor_set(x_1, 2, x_244);
lean_ctor_set(x_1, 1, x_243);
lean_ctor_set(x_1, 0, x_247);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_248);
return x_1;
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; 
x_249 = lean_ctor_get(x_216, 1);
x_250 = lean_ctor_get(x_216, 2);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_216);
x_251 = lean_ctor_get(x_218, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_218, 1);
lean_inc(x_252);
x_253 = lean_ctor_get(x_218, 2);
lean_inc(x_253);
x_254 = lean_ctor_get(x_218, 3);
lean_inc(x_254);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 lean_ctor_release(x_218, 2);
 lean_ctor_release(x_218, 3);
 x_255 = x_218;
} else {
 lean_dec_ref(x_218);
 x_255 = lean_box(0);
}
x_256 = 1;
if (lean_is_scalar(x_255)) {
 x_257 = lean_alloc_ctor(1, 4, 1);
} else {
 x_257 = x_255;
}
lean_ctor_set(x_257, 0, x_217);
lean_ctor_set(x_257, 1, x_249);
lean_ctor_set(x_257, 2, x_250);
lean_ctor_set(x_257, 3, x_251);
lean_ctor_set_uint8(x_257, sizeof(void*)*4, x_256);
x_258 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_258, 0, x_254);
lean_ctor_set(x_258, 1, x_43);
lean_ctor_set(x_258, 2, x_44);
lean_ctor_set(x_258, 3, x_45);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_256);
x_259 = 0;
lean_ctor_set(x_1, 3, x_258);
lean_ctor_set(x_1, 2, x_253);
lean_ctor_set(x_1, 1, x_252);
lean_ctor_set(x_1, 0, x_257);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
else
{
uint8_t x_260; 
x_260 = !lean_is_exclusive(x_216);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; uint8_t x_263; uint8_t x_264; 
x_261 = lean_ctor_get(x_216, 3);
lean_dec(x_261);
x_262 = lean_ctor_get(x_216, 0);
lean_dec(x_262);
x_263 = 0;
lean_ctor_set_uint8(x_216, sizeof(void*)*4, x_263);
x_264 = 1;
lean_ctor_set(x_1, 0, x_216);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_264);
return x_1;
}
else
{
lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; uint8_t x_269; 
x_265 = lean_ctor_get(x_216, 1);
x_266 = lean_ctor_get(x_216, 2);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_216);
x_267 = 0;
x_268 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_268, 0, x_217);
lean_ctor_set(x_268, 1, x_265);
lean_ctor_set(x_268, 2, x_266);
lean_ctor_set(x_268, 3, x_218);
lean_ctor_set_uint8(x_268, sizeof(void*)*4, x_267);
x_269 = 1;
lean_ctor_set(x_1, 0, x_268);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_269);
return x_1;
}
}
}
}
else
{
uint8_t x_270; 
x_270 = lean_ctor_get_uint8(x_217, sizeof(void*)*4);
if (x_270 == 0)
{
uint8_t x_271; 
x_271 = !lean_is_exclusive(x_216);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; 
x_272 = lean_ctor_get(x_216, 1);
x_273 = lean_ctor_get(x_216, 2);
x_274 = lean_ctor_get(x_216, 3);
x_275 = lean_ctor_get(x_216, 0);
lean_dec(x_275);
x_276 = !lean_is_exclusive(x_217);
if (x_276 == 0)
{
uint8_t x_277; uint8_t x_278; 
x_277 = 1;
lean_ctor_set_uint8(x_217, sizeof(void*)*4, x_277);
lean_ctor_set(x_216, 3, x_45);
lean_ctor_set(x_216, 2, x_44);
lean_ctor_set(x_216, 1, x_43);
lean_ctor_set(x_216, 0, x_274);
lean_ctor_set_uint8(x_216, sizeof(void*)*4, x_277);
x_278 = 0;
lean_ctor_set(x_1, 3, x_216);
lean_ctor_set(x_1, 2, x_273);
lean_ctor_set(x_1, 1, x_272);
lean_ctor_set(x_1, 0, x_217);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_278);
return x_1;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; uint8_t x_285; 
x_279 = lean_ctor_get(x_217, 0);
x_280 = lean_ctor_get(x_217, 1);
x_281 = lean_ctor_get(x_217, 2);
x_282 = lean_ctor_get(x_217, 3);
lean_inc(x_282);
lean_inc(x_281);
lean_inc(x_280);
lean_inc(x_279);
lean_dec(x_217);
x_283 = 1;
x_284 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_284, 0, x_279);
lean_ctor_set(x_284, 1, x_280);
lean_ctor_set(x_284, 2, x_281);
lean_ctor_set(x_284, 3, x_282);
lean_ctor_set_uint8(x_284, sizeof(void*)*4, x_283);
lean_ctor_set(x_216, 3, x_45);
lean_ctor_set(x_216, 2, x_44);
lean_ctor_set(x_216, 1, x_43);
lean_ctor_set(x_216, 0, x_274);
lean_ctor_set_uint8(x_216, sizeof(void*)*4, x_283);
x_285 = 0;
lean_ctor_set(x_1, 3, x_216);
lean_ctor_set(x_1, 2, x_273);
lean_ctor_set(x_1, 1, x_272);
lean_ctor_set(x_1, 0, x_284);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_285);
return x_1;
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; uint8_t x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; 
x_286 = lean_ctor_get(x_216, 1);
x_287 = lean_ctor_get(x_216, 2);
x_288 = lean_ctor_get(x_216, 3);
lean_inc(x_288);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_216);
x_289 = lean_ctor_get(x_217, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_217, 1);
lean_inc(x_290);
x_291 = lean_ctor_get(x_217, 2);
lean_inc(x_291);
x_292 = lean_ctor_get(x_217, 3);
lean_inc(x_292);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 lean_ctor_release(x_217, 2);
 lean_ctor_release(x_217, 3);
 x_293 = x_217;
} else {
 lean_dec_ref(x_217);
 x_293 = lean_box(0);
}
x_294 = 1;
if (lean_is_scalar(x_293)) {
 x_295 = lean_alloc_ctor(1, 4, 1);
} else {
 x_295 = x_293;
}
lean_ctor_set(x_295, 0, x_289);
lean_ctor_set(x_295, 1, x_290);
lean_ctor_set(x_295, 2, x_291);
lean_ctor_set(x_295, 3, x_292);
lean_ctor_set_uint8(x_295, sizeof(void*)*4, x_294);
x_296 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_296, 0, x_288);
lean_ctor_set(x_296, 1, x_43);
lean_ctor_set(x_296, 2, x_44);
lean_ctor_set(x_296, 3, x_45);
lean_ctor_set_uint8(x_296, sizeof(void*)*4, x_294);
x_297 = 0;
lean_ctor_set(x_1, 3, x_296);
lean_ctor_set(x_1, 2, x_287);
lean_ctor_set(x_1, 1, x_286);
lean_ctor_set(x_1, 0, x_295);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_297);
return x_1;
}
}
else
{
lean_object* x_298; 
x_298 = lean_ctor_get(x_216, 3);
lean_inc(x_298);
if (lean_obj_tag(x_298) == 0)
{
uint8_t x_299; 
x_299 = !lean_is_exclusive(x_216);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; uint8_t x_302; uint8_t x_303; 
x_300 = lean_ctor_get(x_216, 3);
lean_dec(x_300);
x_301 = lean_ctor_get(x_216, 0);
lean_dec(x_301);
x_302 = 0;
lean_ctor_set_uint8(x_216, sizeof(void*)*4, x_302);
x_303 = 1;
lean_ctor_set(x_1, 0, x_216);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_303);
return x_1;
}
else
{
lean_object* x_304; lean_object* x_305; uint8_t x_306; lean_object* x_307; uint8_t x_308; 
x_304 = lean_ctor_get(x_216, 1);
x_305 = lean_ctor_get(x_216, 2);
lean_inc(x_305);
lean_inc(x_304);
lean_dec(x_216);
x_306 = 0;
x_307 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_307, 0, x_217);
lean_ctor_set(x_307, 1, x_304);
lean_ctor_set(x_307, 2, x_305);
lean_ctor_set(x_307, 3, x_298);
lean_ctor_set_uint8(x_307, sizeof(void*)*4, x_306);
x_308 = 1;
lean_ctor_set(x_1, 0, x_307);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_308);
return x_1;
}
}
else
{
uint8_t x_309; 
x_309 = lean_ctor_get_uint8(x_298, sizeof(void*)*4);
if (x_309 == 0)
{
uint8_t x_310; 
lean_free_object(x_1);
x_310 = !lean_is_exclusive(x_216);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_311 = lean_ctor_get(x_216, 1);
x_312 = lean_ctor_get(x_216, 2);
x_313 = lean_ctor_get(x_216, 3);
lean_dec(x_313);
x_314 = lean_ctor_get(x_216, 0);
lean_dec(x_314);
x_315 = !lean_is_exclusive(x_298);
if (x_315 == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; uint8_t x_321; 
x_316 = lean_ctor_get(x_298, 0);
x_317 = lean_ctor_get(x_298, 1);
x_318 = lean_ctor_get(x_298, 2);
x_319 = lean_ctor_get(x_298, 3);
x_320 = 1;
lean_inc(x_217);
lean_ctor_set(x_298, 3, x_316);
lean_ctor_set(x_298, 2, x_312);
lean_ctor_set(x_298, 1, x_311);
lean_ctor_set(x_298, 0, x_217);
x_321 = !lean_is_exclusive(x_217);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; uint8_t x_326; 
x_322 = lean_ctor_get(x_217, 3);
lean_dec(x_322);
x_323 = lean_ctor_get(x_217, 2);
lean_dec(x_323);
x_324 = lean_ctor_get(x_217, 1);
lean_dec(x_324);
x_325 = lean_ctor_get(x_217, 0);
lean_dec(x_325);
lean_ctor_set_uint8(x_298, sizeof(void*)*4, x_320);
lean_ctor_set(x_217, 3, x_45);
lean_ctor_set(x_217, 2, x_44);
lean_ctor_set(x_217, 1, x_43);
lean_ctor_set(x_217, 0, x_319);
lean_ctor_set_uint8(x_217, sizeof(void*)*4, x_320);
x_326 = 0;
lean_ctor_set(x_216, 3, x_217);
lean_ctor_set(x_216, 2, x_318);
lean_ctor_set(x_216, 1, x_317);
lean_ctor_set(x_216, 0, x_298);
lean_ctor_set_uint8(x_216, sizeof(void*)*4, x_326);
return x_216;
}
else
{
lean_object* x_327; uint8_t x_328; 
lean_dec(x_217);
lean_ctor_set_uint8(x_298, sizeof(void*)*4, x_320);
x_327 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_327, 0, x_319);
lean_ctor_set(x_327, 1, x_43);
lean_ctor_set(x_327, 2, x_44);
lean_ctor_set(x_327, 3, x_45);
lean_ctor_set_uint8(x_327, sizeof(void*)*4, x_320);
x_328 = 0;
lean_ctor_set(x_216, 3, x_327);
lean_ctor_set(x_216, 2, x_318);
lean_ctor_set(x_216, 1, x_317);
lean_ctor_set(x_216, 0, x_298);
lean_ctor_set_uint8(x_216, sizeof(void*)*4, x_328);
return x_216;
}
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; 
x_329 = lean_ctor_get(x_298, 0);
x_330 = lean_ctor_get(x_298, 1);
x_331 = lean_ctor_get(x_298, 2);
x_332 = lean_ctor_get(x_298, 3);
lean_inc(x_332);
lean_inc(x_331);
lean_inc(x_330);
lean_inc(x_329);
lean_dec(x_298);
x_333 = 1;
lean_inc(x_217);
x_334 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_334, 0, x_217);
lean_ctor_set(x_334, 1, x_311);
lean_ctor_set(x_334, 2, x_312);
lean_ctor_set(x_334, 3, x_329);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 lean_ctor_release(x_217, 2);
 lean_ctor_release(x_217, 3);
 x_335 = x_217;
} else {
 lean_dec_ref(x_217);
 x_335 = lean_box(0);
}
lean_ctor_set_uint8(x_334, sizeof(void*)*4, x_333);
if (lean_is_scalar(x_335)) {
 x_336 = lean_alloc_ctor(1, 4, 1);
} else {
 x_336 = x_335;
}
lean_ctor_set(x_336, 0, x_332);
lean_ctor_set(x_336, 1, x_43);
lean_ctor_set(x_336, 2, x_44);
lean_ctor_set(x_336, 3, x_45);
lean_ctor_set_uint8(x_336, sizeof(void*)*4, x_333);
x_337 = 0;
lean_ctor_set(x_216, 3, x_336);
lean_ctor_set(x_216, 2, x_331);
lean_ctor_set(x_216, 1, x_330);
lean_ctor_set(x_216, 0, x_334);
lean_ctor_set_uint8(x_216, sizeof(void*)*4, x_337);
return x_216;
}
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; uint8_t x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; lean_object* x_350; 
x_338 = lean_ctor_get(x_216, 1);
x_339 = lean_ctor_get(x_216, 2);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_216);
x_340 = lean_ctor_get(x_298, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_298, 1);
lean_inc(x_341);
x_342 = lean_ctor_get(x_298, 2);
lean_inc(x_342);
x_343 = lean_ctor_get(x_298, 3);
lean_inc(x_343);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 lean_ctor_release(x_298, 2);
 lean_ctor_release(x_298, 3);
 x_344 = x_298;
} else {
 lean_dec_ref(x_298);
 x_344 = lean_box(0);
}
x_345 = 1;
lean_inc(x_217);
if (lean_is_scalar(x_344)) {
 x_346 = lean_alloc_ctor(1, 4, 1);
} else {
 x_346 = x_344;
}
lean_ctor_set(x_346, 0, x_217);
lean_ctor_set(x_346, 1, x_338);
lean_ctor_set(x_346, 2, x_339);
lean_ctor_set(x_346, 3, x_340);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 lean_ctor_release(x_217, 2);
 lean_ctor_release(x_217, 3);
 x_347 = x_217;
} else {
 lean_dec_ref(x_217);
 x_347 = lean_box(0);
}
lean_ctor_set_uint8(x_346, sizeof(void*)*4, x_345);
if (lean_is_scalar(x_347)) {
 x_348 = lean_alloc_ctor(1, 4, 1);
} else {
 x_348 = x_347;
}
lean_ctor_set(x_348, 0, x_343);
lean_ctor_set(x_348, 1, x_43);
lean_ctor_set(x_348, 2, x_44);
lean_ctor_set(x_348, 3, x_45);
lean_ctor_set_uint8(x_348, sizeof(void*)*4, x_345);
x_349 = 0;
x_350 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_350, 0, x_346);
lean_ctor_set(x_350, 1, x_341);
lean_ctor_set(x_350, 2, x_342);
lean_ctor_set(x_350, 3, x_348);
lean_ctor_set_uint8(x_350, sizeof(void*)*4, x_349);
return x_350;
}
}
else
{
uint8_t x_351; 
x_351 = !lean_is_exclusive(x_216);
if (x_351 == 0)
{
lean_object* x_352; lean_object* x_353; uint8_t x_354; 
x_352 = lean_ctor_get(x_216, 3);
lean_dec(x_352);
x_353 = lean_ctor_get(x_216, 0);
lean_dec(x_353);
x_354 = !lean_is_exclusive(x_217);
if (x_354 == 0)
{
uint8_t x_355; uint8_t x_356; 
lean_ctor_set_uint8(x_217, sizeof(void*)*4, x_309);
x_355 = 0;
lean_ctor_set_uint8(x_216, sizeof(void*)*4, x_355);
x_356 = 1;
lean_ctor_set(x_1, 0, x_216);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_356);
return x_1;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; uint8_t x_363; 
x_357 = lean_ctor_get(x_217, 0);
x_358 = lean_ctor_get(x_217, 1);
x_359 = lean_ctor_get(x_217, 2);
x_360 = lean_ctor_get(x_217, 3);
lean_inc(x_360);
lean_inc(x_359);
lean_inc(x_358);
lean_inc(x_357);
lean_dec(x_217);
x_361 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_361, 0, x_357);
lean_ctor_set(x_361, 1, x_358);
lean_ctor_set(x_361, 2, x_359);
lean_ctor_set(x_361, 3, x_360);
lean_ctor_set_uint8(x_361, sizeof(void*)*4, x_309);
x_362 = 0;
lean_ctor_set(x_216, 0, x_361);
lean_ctor_set_uint8(x_216, sizeof(void*)*4, x_362);
x_363 = 1;
lean_ctor_set(x_1, 0, x_216);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_363);
return x_1;
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; lean_object* x_373; uint8_t x_374; 
x_364 = lean_ctor_get(x_216, 1);
x_365 = lean_ctor_get(x_216, 2);
lean_inc(x_365);
lean_inc(x_364);
lean_dec(x_216);
x_366 = lean_ctor_get(x_217, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_217, 1);
lean_inc(x_367);
x_368 = lean_ctor_get(x_217, 2);
lean_inc(x_368);
x_369 = lean_ctor_get(x_217, 3);
lean_inc(x_369);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 lean_ctor_release(x_217, 2);
 lean_ctor_release(x_217, 3);
 x_370 = x_217;
} else {
 lean_dec_ref(x_217);
 x_370 = lean_box(0);
}
if (lean_is_scalar(x_370)) {
 x_371 = lean_alloc_ctor(1, 4, 1);
} else {
 x_371 = x_370;
}
lean_ctor_set(x_371, 0, x_366);
lean_ctor_set(x_371, 1, x_367);
lean_ctor_set(x_371, 2, x_368);
lean_ctor_set(x_371, 3, x_369);
lean_ctor_set_uint8(x_371, sizeof(void*)*4, x_309);
x_372 = 0;
x_373 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_373, 0, x_371);
lean_ctor_set(x_373, 1, x_364);
lean_ctor_set(x_373, 2, x_365);
lean_ctor_set(x_373, 3, x_298);
lean_ctor_set_uint8(x_373, sizeof(void*)*4, x_372);
x_374 = 1;
lean_ctor_set(x_1, 0, x_373);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_374);
return x_1;
}
}
}
}
}
}
}
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; uint64_t x_379; uint8_t x_380; 
x_375 = lean_ctor_get(x_1, 0);
x_376 = lean_ctor_get(x_1, 1);
x_377 = lean_ctor_get(x_1, 2);
x_378 = lean_ctor_get(x_1, 3);
lean_inc(x_378);
lean_inc(x_377);
lean_inc(x_376);
lean_inc(x_375);
lean_dec(x_1);
x_379 = lean_unbox_uint64(x_376);
x_380 = lean_uint64_dec_lt(x_2, x_379);
if (x_380 == 0)
{
uint64_t x_381; uint8_t x_382; 
x_381 = lean_unbox_uint64(x_376);
x_382 = lean_uint64_dec_eq(x_2, x_381);
if (x_382 == 0)
{
uint8_t x_383; 
x_383 = l_Std_RBNode_isRed___rarg(x_378);
if (x_383 == 0)
{
lean_object* x_384; uint8_t x_385; lean_object* x_386; 
x_384 = l_Std_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2(x_378, x_2, x_3);
x_385 = 1;
x_386 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_386, 0, x_375);
lean_ctor_set(x_386, 1, x_376);
lean_ctor_set(x_386, 2, x_377);
lean_ctor_set(x_386, 3, x_384);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_385);
return x_386;
}
else
{
lean_object* x_387; lean_object* x_388; 
x_387 = l_Std_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2(x_378, x_2, x_3);
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; 
x_389 = lean_ctor_get(x_387, 3);
lean_inc(x_389);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; lean_object* x_394; uint8_t x_395; lean_object* x_396; 
x_390 = lean_ctor_get(x_387, 1);
lean_inc(x_390);
x_391 = lean_ctor_get(x_387, 2);
lean_inc(x_391);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 lean_ctor_release(x_387, 2);
 lean_ctor_release(x_387, 3);
 x_392 = x_387;
} else {
 lean_dec_ref(x_387);
 x_392 = lean_box(0);
}
x_393 = 0;
if (lean_is_scalar(x_392)) {
 x_394 = lean_alloc_ctor(1, 4, 1);
} else {
 x_394 = x_392;
}
lean_ctor_set(x_394, 0, x_389);
lean_ctor_set(x_394, 1, x_390);
lean_ctor_set(x_394, 2, x_391);
lean_ctor_set(x_394, 3, x_389);
lean_ctor_set_uint8(x_394, sizeof(void*)*4, x_393);
x_395 = 1;
x_396 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_396, 0, x_375);
lean_ctor_set(x_396, 1, x_376);
lean_ctor_set(x_396, 2, x_377);
lean_ctor_set(x_396, 3, x_394);
lean_ctor_set_uint8(x_396, sizeof(void*)*4, x_395);
return x_396;
}
else
{
uint8_t x_397; 
x_397 = lean_ctor_get_uint8(x_389, sizeof(void*)*4);
if (x_397 == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; lean_object* x_408; uint8_t x_409; lean_object* x_410; 
x_398 = lean_ctor_get(x_387, 1);
lean_inc(x_398);
x_399 = lean_ctor_get(x_387, 2);
lean_inc(x_399);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 lean_ctor_release(x_387, 2);
 lean_ctor_release(x_387, 3);
 x_400 = x_387;
} else {
 lean_dec_ref(x_387);
 x_400 = lean_box(0);
}
x_401 = lean_ctor_get(x_389, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_389, 1);
lean_inc(x_402);
x_403 = lean_ctor_get(x_389, 2);
lean_inc(x_403);
x_404 = lean_ctor_get(x_389, 3);
lean_inc(x_404);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 lean_ctor_release(x_389, 2);
 lean_ctor_release(x_389, 3);
 x_405 = x_389;
} else {
 lean_dec_ref(x_389);
 x_405 = lean_box(0);
}
x_406 = 1;
if (lean_is_scalar(x_405)) {
 x_407 = lean_alloc_ctor(1, 4, 1);
} else {
 x_407 = x_405;
}
lean_ctor_set(x_407, 0, x_375);
lean_ctor_set(x_407, 1, x_376);
lean_ctor_set(x_407, 2, x_377);
lean_ctor_set(x_407, 3, x_388);
lean_ctor_set_uint8(x_407, sizeof(void*)*4, x_406);
if (lean_is_scalar(x_400)) {
 x_408 = lean_alloc_ctor(1, 4, 1);
} else {
 x_408 = x_400;
}
lean_ctor_set(x_408, 0, x_401);
lean_ctor_set(x_408, 1, x_402);
lean_ctor_set(x_408, 2, x_403);
lean_ctor_set(x_408, 3, x_404);
lean_ctor_set_uint8(x_408, sizeof(void*)*4, x_406);
x_409 = 0;
x_410 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_410, 0, x_407);
lean_ctor_set(x_410, 1, x_398);
lean_ctor_set(x_410, 2, x_399);
lean_ctor_set(x_410, 3, x_408);
lean_ctor_set_uint8(x_410, sizeof(void*)*4, x_409);
return x_410;
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; uint8_t x_414; lean_object* x_415; uint8_t x_416; lean_object* x_417; 
x_411 = lean_ctor_get(x_387, 1);
lean_inc(x_411);
x_412 = lean_ctor_get(x_387, 2);
lean_inc(x_412);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 lean_ctor_release(x_387, 2);
 lean_ctor_release(x_387, 3);
 x_413 = x_387;
} else {
 lean_dec_ref(x_387);
 x_413 = lean_box(0);
}
x_414 = 0;
if (lean_is_scalar(x_413)) {
 x_415 = lean_alloc_ctor(1, 4, 1);
} else {
 x_415 = x_413;
}
lean_ctor_set(x_415, 0, x_388);
lean_ctor_set(x_415, 1, x_411);
lean_ctor_set(x_415, 2, x_412);
lean_ctor_set(x_415, 3, x_389);
lean_ctor_set_uint8(x_415, sizeof(void*)*4, x_414);
x_416 = 1;
x_417 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_417, 0, x_375);
lean_ctor_set(x_417, 1, x_376);
lean_ctor_set(x_417, 2, x_377);
lean_ctor_set(x_417, 3, x_415);
lean_ctor_set_uint8(x_417, sizeof(void*)*4, x_416);
return x_417;
}
}
}
else
{
uint8_t x_418; 
x_418 = lean_ctor_get_uint8(x_388, sizeof(void*)*4);
if (x_418 == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; uint8_t x_428; lean_object* x_429; lean_object* x_430; uint8_t x_431; lean_object* x_432; 
x_419 = lean_ctor_get(x_387, 1);
lean_inc(x_419);
x_420 = lean_ctor_get(x_387, 2);
lean_inc(x_420);
x_421 = lean_ctor_get(x_387, 3);
lean_inc(x_421);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 lean_ctor_release(x_387, 2);
 lean_ctor_release(x_387, 3);
 x_422 = x_387;
} else {
 lean_dec_ref(x_387);
 x_422 = lean_box(0);
}
x_423 = lean_ctor_get(x_388, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_388, 1);
lean_inc(x_424);
x_425 = lean_ctor_get(x_388, 2);
lean_inc(x_425);
x_426 = lean_ctor_get(x_388, 3);
lean_inc(x_426);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 lean_ctor_release(x_388, 1);
 lean_ctor_release(x_388, 2);
 lean_ctor_release(x_388, 3);
 x_427 = x_388;
} else {
 lean_dec_ref(x_388);
 x_427 = lean_box(0);
}
x_428 = 1;
if (lean_is_scalar(x_427)) {
 x_429 = lean_alloc_ctor(1, 4, 1);
} else {
 x_429 = x_427;
}
lean_ctor_set(x_429, 0, x_375);
lean_ctor_set(x_429, 1, x_376);
lean_ctor_set(x_429, 2, x_377);
lean_ctor_set(x_429, 3, x_423);
lean_ctor_set_uint8(x_429, sizeof(void*)*4, x_428);
if (lean_is_scalar(x_422)) {
 x_430 = lean_alloc_ctor(1, 4, 1);
} else {
 x_430 = x_422;
}
lean_ctor_set(x_430, 0, x_426);
lean_ctor_set(x_430, 1, x_419);
lean_ctor_set(x_430, 2, x_420);
lean_ctor_set(x_430, 3, x_421);
lean_ctor_set_uint8(x_430, sizeof(void*)*4, x_428);
x_431 = 0;
x_432 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_432, 0, x_429);
lean_ctor_set(x_432, 1, x_424);
lean_ctor_set(x_432, 2, x_425);
lean_ctor_set(x_432, 3, x_430);
lean_ctor_set_uint8(x_432, sizeof(void*)*4, x_431);
return x_432;
}
else
{
lean_object* x_433; 
x_433 = lean_ctor_get(x_387, 3);
lean_inc(x_433);
if (lean_obj_tag(x_433) == 0)
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; uint8_t x_437; lean_object* x_438; uint8_t x_439; lean_object* x_440; 
x_434 = lean_ctor_get(x_387, 1);
lean_inc(x_434);
x_435 = lean_ctor_get(x_387, 2);
lean_inc(x_435);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 lean_ctor_release(x_387, 2);
 lean_ctor_release(x_387, 3);
 x_436 = x_387;
} else {
 lean_dec_ref(x_387);
 x_436 = lean_box(0);
}
x_437 = 0;
if (lean_is_scalar(x_436)) {
 x_438 = lean_alloc_ctor(1, 4, 1);
} else {
 x_438 = x_436;
}
lean_ctor_set(x_438, 0, x_388);
lean_ctor_set(x_438, 1, x_434);
lean_ctor_set(x_438, 2, x_435);
lean_ctor_set(x_438, 3, x_433);
lean_ctor_set_uint8(x_438, sizeof(void*)*4, x_437);
x_439 = 1;
x_440 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_440, 0, x_375);
lean_ctor_set(x_440, 1, x_376);
lean_ctor_set(x_440, 2, x_377);
lean_ctor_set(x_440, 3, x_438);
lean_ctor_set_uint8(x_440, sizeof(void*)*4, x_439);
return x_440;
}
else
{
uint8_t x_441; 
x_441 = lean_ctor_get_uint8(x_433, sizeof(void*)*4);
if (x_441 == 0)
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; uint8_t x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; lean_object* x_455; 
x_442 = lean_ctor_get(x_387, 1);
lean_inc(x_442);
x_443 = lean_ctor_get(x_387, 2);
lean_inc(x_443);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 lean_ctor_release(x_387, 2);
 lean_ctor_release(x_387, 3);
 x_444 = x_387;
} else {
 lean_dec_ref(x_387);
 x_444 = lean_box(0);
}
x_445 = lean_ctor_get(x_433, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_433, 1);
lean_inc(x_446);
x_447 = lean_ctor_get(x_433, 2);
lean_inc(x_447);
x_448 = lean_ctor_get(x_433, 3);
lean_inc(x_448);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 lean_ctor_release(x_433, 2);
 lean_ctor_release(x_433, 3);
 x_449 = x_433;
} else {
 lean_dec_ref(x_433);
 x_449 = lean_box(0);
}
x_450 = 1;
lean_inc(x_388);
if (lean_is_scalar(x_449)) {
 x_451 = lean_alloc_ctor(1, 4, 1);
} else {
 x_451 = x_449;
}
lean_ctor_set(x_451, 0, x_375);
lean_ctor_set(x_451, 1, x_376);
lean_ctor_set(x_451, 2, x_377);
lean_ctor_set(x_451, 3, x_388);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 lean_ctor_release(x_388, 1);
 lean_ctor_release(x_388, 2);
 lean_ctor_release(x_388, 3);
 x_452 = x_388;
} else {
 lean_dec_ref(x_388);
 x_452 = lean_box(0);
}
lean_ctor_set_uint8(x_451, sizeof(void*)*4, x_450);
if (lean_is_scalar(x_452)) {
 x_453 = lean_alloc_ctor(1, 4, 1);
} else {
 x_453 = x_452;
}
lean_ctor_set(x_453, 0, x_445);
lean_ctor_set(x_453, 1, x_446);
lean_ctor_set(x_453, 2, x_447);
lean_ctor_set(x_453, 3, x_448);
lean_ctor_set_uint8(x_453, sizeof(void*)*4, x_450);
x_454 = 0;
if (lean_is_scalar(x_444)) {
 x_455 = lean_alloc_ctor(1, 4, 1);
} else {
 x_455 = x_444;
}
lean_ctor_set(x_455, 0, x_451);
lean_ctor_set(x_455, 1, x_442);
lean_ctor_set(x_455, 2, x_443);
lean_ctor_set(x_455, 3, x_453);
lean_ctor_set_uint8(x_455, sizeof(void*)*4, x_454);
return x_455;
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; lean_object* x_466; uint8_t x_467; lean_object* x_468; 
x_456 = lean_ctor_get(x_387, 1);
lean_inc(x_456);
x_457 = lean_ctor_get(x_387, 2);
lean_inc(x_457);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 lean_ctor_release(x_387, 2);
 lean_ctor_release(x_387, 3);
 x_458 = x_387;
} else {
 lean_dec_ref(x_387);
 x_458 = lean_box(0);
}
x_459 = lean_ctor_get(x_388, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_388, 1);
lean_inc(x_460);
x_461 = lean_ctor_get(x_388, 2);
lean_inc(x_461);
x_462 = lean_ctor_get(x_388, 3);
lean_inc(x_462);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 lean_ctor_release(x_388, 1);
 lean_ctor_release(x_388, 2);
 lean_ctor_release(x_388, 3);
 x_463 = x_388;
} else {
 lean_dec_ref(x_388);
 x_463 = lean_box(0);
}
if (lean_is_scalar(x_463)) {
 x_464 = lean_alloc_ctor(1, 4, 1);
} else {
 x_464 = x_463;
}
lean_ctor_set(x_464, 0, x_459);
lean_ctor_set(x_464, 1, x_460);
lean_ctor_set(x_464, 2, x_461);
lean_ctor_set(x_464, 3, x_462);
lean_ctor_set_uint8(x_464, sizeof(void*)*4, x_441);
x_465 = 0;
if (lean_is_scalar(x_458)) {
 x_466 = lean_alloc_ctor(1, 4, 1);
} else {
 x_466 = x_458;
}
lean_ctor_set(x_466, 0, x_464);
lean_ctor_set(x_466, 1, x_456);
lean_ctor_set(x_466, 2, x_457);
lean_ctor_set(x_466, 3, x_433);
lean_ctor_set_uint8(x_466, sizeof(void*)*4, x_465);
x_467 = 1;
x_468 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_468, 0, x_375);
lean_ctor_set(x_468, 1, x_376);
lean_ctor_set(x_468, 2, x_377);
lean_ctor_set(x_468, 3, x_466);
lean_ctor_set_uint8(x_468, sizeof(void*)*4, x_467);
return x_468;
}
}
}
}
}
}
else
{
uint8_t x_469; lean_object* x_470; lean_object* x_471; 
lean_dec(x_377);
lean_dec(x_376);
x_469 = 1;
x_470 = lean_box_uint64(x_2);
x_471 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_471, 0, x_375);
lean_ctor_set(x_471, 1, x_470);
lean_ctor_set(x_471, 2, x_3);
lean_ctor_set(x_471, 3, x_378);
lean_ctor_set_uint8(x_471, sizeof(void*)*4, x_469);
return x_471;
}
}
else
{
uint8_t x_472; 
x_472 = l_Std_RBNode_isRed___rarg(x_375);
if (x_472 == 0)
{
lean_object* x_473; uint8_t x_474; lean_object* x_475; 
x_473 = l_Std_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2(x_375, x_2, x_3);
x_474 = 1;
x_475 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_475, 0, x_473);
lean_ctor_set(x_475, 1, x_376);
lean_ctor_set(x_475, 2, x_377);
lean_ctor_set(x_475, 3, x_378);
lean_ctor_set_uint8(x_475, sizeof(void*)*4, x_474);
return x_475;
}
else
{
lean_object* x_476; lean_object* x_477; 
x_476 = l_Std_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2(x_375, x_2, x_3);
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
if (lean_obj_tag(x_477) == 0)
{
lean_object* x_478; 
x_478 = lean_ctor_get(x_476, 3);
lean_inc(x_478);
if (lean_obj_tag(x_478) == 0)
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; uint8_t x_482; lean_object* x_483; uint8_t x_484; lean_object* x_485; 
x_479 = lean_ctor_get(x_476, 1);
lean_inc(x_479);
x_480 = lean_ctor_get(x_476, 2);
lean_inc(x_480);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 lean_ctor_release(x_476, 1);
 lean_ctor_release(x_476, 2);
 lean_ctor_release(x_476, 3);
 x_481 = x_476;
} else {
 lean_dec_ref(x_476);
 x_481 = lean_box(0);
}
x_482 = 0;
if (lean_is_scalar(x_481)) {
 x_483 = lean_alloc_ctor(1, 4, 1);
} else {
 x_483 = x_481;
}
lean_ctor_set(x_483, 0, x_478);
lean_ctor_set(x_483, 1, x_479);
lean_ctor_set(x_483, 2, x_480);
lean_ctor_set(x_483, 3, x_478);
lean_ctor_set_uint8(x_483, sizeof(void*)*4, x_482);
x_484 = 1;
x_485 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_485, 0, x_483);
lean_ctor_set(x_485, 1, x_376);
lean_ctor_set(x_485, 2, x_377);
lean_ctor_set(x_485, 3, x_378);
lean_ctor_set_uint8(x_485, sizeof(void*)*4, x_484);
return x_485;
}
else
{
uint8_t x_486; 
x_486 = lean_ctor_get_uint8(x_478, sizeof(void*)*4);
if (x_486 == 0)
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; uint8_t x_495; lean_object* x_496; lean_object* x_497; uint8_t x_498; lean_object* x_499; 
x_487 = lean_ctor_get(x_476, 1);
lean_inc(x_487);
x_488 = lean_ctor_get(x_476, 2);
lean_inc(x_488);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 lean_ctor_release(x_476, 1);
 lean_ctor_release(x_476, 2);
 lean_ctor_release(x_476, 3);
 x_489 = x_476;
} else {
 lean_dec_ref(x_476);
 x_489 = lean_box(0);
}
x_490 = lean_ctor_get(x_478, 0);
lean_inc(x_490);
x_491 = lean_ctor_get(x_478, 1);
lean_inc(x_491);
x_492 = lean_ctor_get(x_478, 2);
lean_inc(x_492);
x_493 = lean_ctor_get(x_478, 3);
lean_inc(x_493);
if (lean_is_exclusive(x_478)) {
 lean_ctor_release(x_478, 0);
 lean_ctor_release(x_478, 1);
 lean_ctor_release(x_478, 2);
 lean_ctor_release(x_478, 3);
 x_494 = x_478;
} else {
 lean_dec_ref(x_478);
 x_494 = lean_box(0);
}
x_495 = 1;
if (lean_is_scalar(x_494)) {
 x_496 = lean_alloc_ctor(1, 4, 1);
} else {
 x_496 = x_494;
}
lean_ctor_set(x_496, 0, x_477);
lean_ctor_set(x_496, 1, x_487);
lean_ctor_set(x_496, 2, x_488);
lean_ctor_set(x_496, 3, x_490);
lean_ctor_set_uint8(x_496, sizeof(void*)*4, x_495);
if (lean_is_scalar(x_489)) {
 x_497 = lean_alloc_ctor(1, 4, 1);
} else {
 x_497 = x_489;
}
lean_ctor_set(x_497, 0, x_493);
lean_ctor_set(x_497, 1, x_376);
lean_ctor_set(x_497, 2, x_377);
lean_ctor_set(x_497, 3, x_378);
lean_ctor_set_uint8(x_497, sizeof(void*)*4, x_495);
x_498 = 0;
x_499 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_499, 0, x_496);
lean_ctor_set(x_499, 1, x_491);
lean_ctor_set(x_499, 2, x_492);
lean_ctor_set(x_499, 3, x_497);
lean_ctor_set_uint8(x_499, sizeof(void*)*4, x_498);
return x_499;
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; uint8_t x_503; lean_object* x_504; uint8_t x_505; lean_object* x_506; 
x_500 = lean_ctor_get(x_476, 1);
lean_inc(x_500);
x_501 = lean_ctor_get(x_476, 2);
lean_inc(x_501);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 lean_ctor_release(x_476, 1);
 lean_ctor_release(x_476, 2);
 lean_ctor_release(x_476, 3);
 x_502 = x_476;
} else {
 lean_dec_ref(x_476);
 x_502 = lean_box(0);
}
x_503 = 0;
if (lean_is_scalar(x_502)) {
 x_504 = lean_alloc_ctor(1, 4, 1);
} else {
 x_504 = x_502;
}
lean_ctor_set(x_504, 0, x_477);
lean_ctor_set(x_504, 1, x_500);
lean_ctor_set(x_504, 2, x_501);
lean_ctor_set(x_504, 3, x_478);
lean_ctor_set_uint8(x_504, sizeof(void*)*4, x_503);
x_505 = 1;
x_506 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_506, 0, x_504);
lean_ctor_set(x_506, 1, x_376);
lean_ctor_set(x_506, 2, x_377);
lean_ctor_set(x_506, 3, x_378);
lean_ctor_set_uint8(x_506, sizeof(void*)*4, x_505);
return x_506;
}
}
}
else
{
uint8_t x_507; 
x_507 = lean_ctor_get_uint8(x_477, sizeof(void*)*4);
if (x_507 == 0)
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; uint8_t x_517; lean_object* x_518; lean_object* x_519; uint8_t x_520; lean_object* x_521; 
x_508 = lean_ctor_get(x_476, 1);
lean_inc(x_508);
x_509 = lean_ctor_get(x_476, 2);
lean_inc(x_509);
x_510 = lean_ctor_get(x_476, 3);
lean_inc(x_510);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 lean_ctor_release(x_476, 1);
 lean_ctor_release(x_476, 2);
 lean_ctor_release(x_476, 3);
 x_511 = x_476;
} else {
 lean_dec_ref(x_476);
 x_511 = lean_box(0);
}
x_512 = lean_ctor_get(x_477, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_477, 1);
lean_inc(x_513);
x_514 = lean_ctor_get(x_477, 2);
lean_inc(x_514);
x_515 = lean_ctor_get(x_477, 3);
lean_inc(x_515);
if (lean_is_exclusive(x_477)) {
 lean_ctor_release(x_477, 0);
 lean_ctor_release(x_477, 1);
 lean_ctor_release(x_477, 2);
 lean_ctor_release(x_477, 3);
 x_516 = x_477;
} else {
 lean_dec_ref(x_477);
 x_516 = lean_box(0);
}
x_517 = 1;
if (lean_is_scalar(x_516)) {
 x_518 = lean_alloc_ctor(1, 4, 1);
} else {
 x_518 = x_516;
}
lean_ctor_set(x_518, 0, x_512);
lean_ctor_set(x_518, 1, x_513);
lean_ctor_set(x_518, 2, x_514);
lean_ctor_set(x_518, 3, x_515);
lean_ctor_set_uint8(x_518, sizeof(void*)*4, x_517);
if (lean_is_scalar(x_511)) {
 x_519 = lean_alloc_ctor(1, 4, 1);
} else {
 x_519 = x_511;
}
lean_ctor_set(x_519, 0, x_510);
lean_ctor_set(x_519, 1, x_376);
lean_ctor_set(x_519, 2, x_377);
lean_ctor_set(x_519, 3, x_378);
lean_ctor_set_uint8(x_519, sizeof(void*)*4, x_517);
x_520 = 0;
x_521 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_521, 0, x_518);
lean_ctor_set(x_521, 1, x_508);
lean_ctor_set(x_521, 2, x_509);
lean_ctor_set(x_521, 3, x_519);
lean_ctor_set_uint8(x_521, sizeof(void*)*4, x_520);
return x_521;
}
else
{
lean_object* x_522; 
x_522 = lean_ctor_get(x_476, 3);
lean_inc(x_522);
if (lean_obj_tag(x_522) == 0)
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; lean_object* x_527; uint8_t x_528; lean_object* x_529; 
x_523 = lean_ctor_get(x_476, 1);
lean_inc(x_523);
x_524 = lean_ctor_get(x_476, 2);
lean_inc(x_524);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 lean_ctor_release(x_476, 1);
 lean_ctor_release(x_476, 2);
 lean_ctor_release(x_476, 3);
 x_525 = x_476;
} else {
 lean_dec_ref(x_476);
 x_525 = lean_box(0);
}
x_526 = 0;
if (lean_is_scalar(x_525)) {
 x_527 = lean_alloc_ctor(1, 4, 1);
} else {
 x_527 = x_525;
}
lean_ctor_set(x_527, 0, x_477);
lean_ctor_set(x_527, 1, x_523);
lean_ctor_set(x_527, 2, x_524);
lean_ctor_set(x_527, 3, x_522);
lean_ctor_set_uint8(x_527, sizeof(void*)*4, x_526);
x_528 = 1;
x_529 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_529, 0, x_527);
lean_ctor_set(x_529, 1, x_376);
lean_ctor_set(x_529, 2, x_377);
lean_ctor_set(x_529, 3, x_378);
lean_ctor_set_uint8(x_529, sizeof(void*)*4, x_528);
return x_529;
}
else
{
uint8_t x_530; 
x_530 = lean_ctor_get_uint8(x_522, sizeof(void*)*4);
if (x_530 == 0)
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; uint8_t x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; uint8_t x_543; lean_object* x_544; 
x_531 = lean_ctor_get(x_476, 1);
lean_inc(x_531);
x_532 = lean_ctor_get(x_476, 2);
lean_inc(x_532);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 lean_ctor_release(x_476, 1);
 lean_ctor_release(x_476, 2);
 lean_ctor_release(x_476, 3);
 x_533 = x_476;
} else {
 lean_dec_ref(x_476);
 x_533 = lean_box(0);
}
x_534 = lean_ctor_get(x_522, 0);
lean_inc(x_534);
x_535 = lean_ctor_get(x_522, 1);
lean_inc(x_535);
x_536 = lean_ctor_get(x_522, 2);
lean_inc(x_536);
x_537 = lean_ctor_get(x_522, 3);
lean_inc(x_537);
if (lean_is_exclusive(x_522)) {
 lean_ctor_release(x_522, 0);
 lean_ctor_release(x_522, 1);
 lean_ctor_release(x_522, 2);
 lean_ctor_release(x_522, 3);
 x_538 = x_522;
} else {
 lean_dec_ref(x_522);
 x_538 = lean_box(0);
}
x_539 = 1;
lean_inc(x_477);
if (lean_is_scalar(x_538)) {
 x_540 = lean_alloc_ctor(1, 4, 1);
} else {
 x_540 = x_538;
}
lean_ctor_set(x_540, 0, x_477);
lean_ctor_set(x_540, 1, x_531);
lean_ctor_set(x_540, 2, x_532);
lean_ctor_set(x_540, 3, x_534);
if (lean_is_exclusive(x_477)) {
 lean_ctor_release(x_477, 0);
 lean_ctor_release(x_477, 1);
 lean_ctor_release(x_477, 2);
 lean_ctor_release(x_477, 3);
 x_541 = x_477;
} else {
 lean_dec_ref(x_477);
 x_541 = lean_box(0);
}
lean_ctor_set_uint8(x_540, sizeof(void*)*4, x_539);
if (lean_is_scalar(x_541)) {
 x_542 = lean_alloc_ctor(1, 4, 1);
} else {
 x_542 = x_541;
}
lean_ctor_set(x_542, 0, x_537);
lean_ctor_set(x_542, 1, x_376);
lean_ctor_set(x_542, 2, x_377);
lean_ctor_set(x_542, 3, x_378);
lean_ctor_set_uint8(x_542, sizeof(void*)*4, x_539);
x_543 = 0;
if (lean_is_scalar(x_533)) {
 x_544 = lean_alloc_ctor(1, 4, 1);
} else {
 x_544 = x_533;
}
lean_ctor_set(x_544, 0, x_540);
lean_ctor_set(x_544, 1, x_535);
lean_ctor_set(x_544, 2, x_536);
lean_ctor_set(x_544, 3, x_542);
lean_ctor_set_uint8(x_544, sizeof(void*)*4, x_543);
return x_544;
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; uint8_t x_554; lean_object* x_555; uint8_t x_556; lean_object* x_557; 
x_545 = lean_ctor_get(x_476, 1);
lean_inc(x_545);
x_546 = lean_ctor_get(x_476, 2);
lean_inc(x_546);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 lean_ctor_release(x_476, 1);
 lean_ctor_release(x_476, 2);
 lean_ctor_release(x_476, 3);
 x_547 = x_476;
} else {
 lean_dec_ref(x_476);
 x_547 = lean_box(0);
}
x_548 = lean_ctor_get(x_477, 0);
lean_inc(x_548);
x_549 = lean_ctor_get(x_477, 1);
lean_inc(x_549);
x_550 = lean_ctor_get(x_477, 2);
lean_inc(x_550);
x_551 = lean_ctor_get(x_477, 3);
lean_inc(x_551);
if (lean_is_exclusive(x_477)) {
 lean_ctor_release(x_477, 0);
 lean_ctor_release(x_477, 1);
 lean_ctor_release(x_477, 2);
 lean_ctor_release(x_477, 3);
 x_552 = x_477;
} else {
 lean_dec_ref(x_477);
 x_552 = lean_box(0);
}
if (lean_is_scalar(x_552)) {
 x_553 = lean_alloc_ctor(1, 4, 1);
} else {
 x_553 = x_552;
}
lean_ctor_set(x_553, 0, x_548);
lean_ctor_set(x_553, 1, x_549);
lean_ctor_set(x_553, 2, x_550);
lean_ctor_set(x_553, 3, x_551);
lean_ctor_set_uint8(x_553, sizeof(void*)*4, x_530);
x_554 = 0;
if (lean_is_scalar(x_547)) {
 x_555 = lean_alloc_ctor(1, 4, 1);
} else {
 x_555 = x_547;
}
lean_ctor_set(x_555, 0, x_553);
lean_ctor_set(x_555, 1, x_545);
lean_ctor_set(x_555, 2, x_546);
lean_ctor_set(x_555, 3, x_522);
lean_ctor_set_uint8(x_555, sizeof(void*)*4, x_554);
x_556 = 1;
x_557 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_557, 0, x_555);
lean_ctor_set(x_557, 1, x_376);
lean_ctor_set(x_557, 2, x_377);
lean_ctor_set(x_557, 3, x_378);
lean_ctor_set_uint8(x_557, sizeof(void*)*4, x_556);
return x_557;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_insert___at_Lean_Server_FileWorker_handleRpcConnect___spec__1(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Std_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2(x_1, x_2, x_3);
x_7 = l_Std_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcConnect___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_FileWorker_RpcSession_new(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_st_mk_ref(x_7, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_take(x_1, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_12, 2);
x_16 = lean_unbox_uint64(x_6);
x_17 = l_Std_RBNode_insert___at_Lean_Server_FileWorker_handleRpcConnect___spec__1(x_15, x_16, x_9);
lean_ctor_set(x_12, 2, x_17);
x_18 = lean_st_ref_set(x_1, x_12, x_13);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_6);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
x_25 = lean_ctor_get(x_12, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_26 = lean_unbox_uint64(x_6);
x_27 = l_Std_RBNode_insert___at_Lean_Server_FileWorker_handleRpcConnect___spec__1(x_25, x_26, x_9);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_st_ref_set(x_1, x_28, x_13);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_6);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_3);
if (x_33 == 0)
{
return x_3;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_3, 0);
x_35 = lean_ctor_get(x_3, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_3);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcConnect(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleRpcConnect___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Std_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_insert___at_Lean_Server_FileWorker_handleRpcConnect___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Std_RBNode_insert___at_Lean_Server_FileWorker_handleRpcConnect___spec__1(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcConnect___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_FileWorker_handleRpcConnect___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcConnect___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_FileWorker_handleRpcConnect(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_parseParams___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Got param with wrong structure: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_parseParams___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\n");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_2);
x_6 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Json_compress(x_2);
x_9 = l_Lean_Server_FileWorker_parseParams___rarg___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Lean_Server_FileWorker_parseParams___rarg___closed__2;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_string_append(x_12, x_7);
lean_dec(x_7);
x_14 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_IO_throwServerError___rarg(x_15, x_5);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_17 = lean_ctor_get(x_6, 0);
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_parseParams___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_parseParams___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcKeepAliveParams____x40_Lean_Data_Lsp_Extra___hyg_1585_(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Json_compress(x_1);
x_8 = l_Lean_Server_FileWorker_parseParams___rarg___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lean_Server_FileWorker_parseParams___rarg___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_6);
lean_dec(x_6);
x_13 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_IO_throwServerError___rarg(x_14, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcReleaseParams____x40_Lean_Data_Lsp_Extra___hyg_1446_(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Json_compress(x_1);
x_8 = l_Lean_Server_FileWorker_parseParams___rarg___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lean_Server_FileWorker_parseParams___rarg___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_6);
lean_dec(x_6);
x_13 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_IO_throwServerError___rarg(x_14, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonCancelParams____x40_Lean_Data_Lsp_Basic___hyg_109_(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Json_compress(x_1);
x_8 = l_Lean_Server_FileWorker_parseParams___rarg___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lean_Server_FileWorker_parseParams___rarg___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_6);
lean_dec(x_6);
x_13 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_IO_throwServerError___rarg(x_14, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_fromJsonDidChangeTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_422_(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Json_compress(x_1);
x_8 = l_Lean_Server_FileWorker_parseParams___rarg___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lean_Server_FileWorker_parseParams___rarg___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_6);
lean_dec(x_6);
x_13 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_IO_throwServerError___rarg(x_14, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleNotification___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("textDocument/didChange");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleNotification___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("$/cancelRequest");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleNotification___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("$/lean/rpc/release");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleNotification___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("$/lean/rpc/keepAlive");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleNotification___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Got unsupported notification method: ");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleNotification(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Server_FileWorker_handleNotification___closed__1;
x_7 = lean_string_dec_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Server_FileWorker_handleNotification___closed__2;
x_9 = lean_string_dec_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Server_FileWorker_handleNotification___closed__3;
x_11 = lean_string_dec_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Server_FileWorker_handleNotification___closed__4;
x_13 = lean_string_dec_eq(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = l_Lean_Server_FileWorker_handleNotification___closed__5;
x_15 = lean_string_append(x_14, x_1);
x_16 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = l_IO_throwServerError___rarg(x_17, x_5);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__1(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Server_FileWorker_handleRpcKeepAlive(x_20, x_3, x_4, x_21);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_20);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_4);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
else
{
lean_object* x_27; 
x_27 = l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__2(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Server_FileWorker_handleRpcRelease(x_28, x_3, x_4, x_29);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_28);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_4);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_27);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
else
{
lean_object* x_35; 
x_35 = l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__3(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Server_FileWorker_handleCancelRequest(x_36, x_3, x_4, x_37);
lean_dec(x_4);
lean_dec(x_3);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_4);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_35, 0);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_35);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
lean_object* x_43; 
x_43 = l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__4(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Server_FileWorker_handleDidChange(x_44, x_3, x_4, x_45);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_4);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_43);
if (x_47 == 0)
{
return x_43;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_43, 0);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_43);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleNotification___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_handleNotification(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Server_FileWorker_queueRequest___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = 0;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_inc(x_2);
x_13 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_118_(x_2, x_10);
switch (x_13) {
case 0:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Std_RBNode_ins___at_Lean_Server_FileWorker_queueRequest___spec__2(x_9, x_2, x_3);
x_15 = 0;
lean_ctor_set(x_1, 0, x_14);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_15);
return x_1;
}
case 1:
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_16);
return x_1;
}
default: 
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Std_RBNode_ins___at_Lean_Server_FileWorker_queueRequest___spec__2(x_12, x_2, x_3);
x_18 = 0;
lean_ctor_set(x_1, 3, x_17);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_18);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_1, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
lean_inc(x_20);
lean_inc(x_2);
x_23 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_118_(x_2, x_20);
switch (x_23) {
case 0:
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = l_Std_RBNode_ins___at_Lean_Server_FileWorker_queueRequest___spec__2(x_19, x_2, x_3);
x_25 = 0;
x_26 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 3, x_22);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_25);
return x_26;
}
case 1:
{
uint8_t x_27; lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_20);
x_27 = 0;
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 2, x_3);
lean_ctor_set(x_28, 3, x_22);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_27);
return x_28;
}
default: 
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = l_Std_RBNode_ins___at_Lean_Server_FileWorker_queueRequest___spec__2(x_22, x_2, x_3);
x_30 = 0;
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_20);
lean_ctor_set(x_31, 2, x_21);
lean_ctor_set(x_31, 3, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_30);
return x_31;
}
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_ctor_get(x_1, 1);
x_35 = lean_ctor_get(x_1, 2);
x_36 = lean_ctor_get(x_1, 3);
lean_inc(x_34);
lean_inc(x_2);
x_37 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_118_(x_2, x_34);
switch (x_37) {
case 0:
{
uint8_t x_38; 
x_38 = l_Std_RBNode_isRed___rarg(x_33);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Std_RBNode_ins___at_Lean_Server_FileWorker_queueRequest___spec__2(x_33, x_2, x_3);
x_40 = 1;
lean_ctor_set(x_1, 0, x_39);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_40);
return x_1;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Std_RBNode_ins___at_Lean_Server_FileWorker_queueRequest___spec__2(x_33, x_2, x_3);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 3);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_41, 3);
lean_dec(x_45);
x_46 = lean_ctor_get(x_41, 0);
lean_dec(x_46);
x_47 = 0;
lean_ctor_set(x_41, 0, x_43);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_47);
x_48 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_48);
return x_1;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_41, 1);
x_50 = lean_ctor_get(x_41, 2);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_41);
x_51 = 0;
x_52 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_49);
lean_ctor_set(x_52, 2, x_50);
lean_ctor_set(x_52, 3, x_43);
lean_ctor_set_uint8(x_52, sizeof(void*)*4, x_51);
x_53 = 1;
lean_ctor_set(x_1, 0, x_52);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_53);
return x_1;
}
}
else
{
uint8_t x_54; 
x_54 = lean_ctor_get_uint8(x_43, sizeof(void*)*4);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_41);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_41, 1);
x_57 = lean_ctor_get(x_41, 2);
x_58 = lean_ctor_get(x_41, 3);
lean_dec(x_58);
x_59 = lean_ctor_get(x_41, 0);
lean_dec(x_59);
x_60 = !lean_is_exclusive(x_43);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_43, 0);
x_62 = lean_ctor_get(x_43, 1);
x_63 = lean_ctor_get(x_43, 2);
x_64 = lean_ctor_get(x_43, 3);
x_65 = 1;
lean_ctor_set(x_43, 3, x_61);
lean_ctor_set(x_43, 2, x_57);
lean_ctor_set(x_43, 1, x_56);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_65);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_64);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_65);
x_66 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_63);
lean_ctor_set(x_1, 1, x_62);
lean_ctor_set(x_1, 0, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_66);
return x_1;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; uint8_t x_73; 
x_67 = lean_ctor_get(x_43, 0);
x_68 = lean_ctor_get(x_43, 1);
x_69 = lean_ctor_get(x_43, 2);
x_70 = lean_ctor_get(x_43, 3);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_43);
x_71 = 1;
x_72 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_72, 0, x_42);
lean_ctor_set(x_72, 1, x_56);
lean_ctor_set(x_72, 2, x_57);
lean_ctor_set(x_72, 3, x_67);
lean_ctor_set_uint8(x_72, sizeof(void*)*4, x_71);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_70);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_71);
x_73 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_69);
lean_ctor_set(x_1, 1, x_68);
lean_ctor_set(x_1, 0, x_72);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_73);
return x_1;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_74 = lean_ctor_get(x_41, 1);
x_75 = lean_ctor_get(x_41, 2);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_41);
x_76 = lean_ctor_get(x_43, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_43, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_43, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_43, 3);
lean_inc(x_79);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 x_80 = x_43;
} else {
 lean_dec_ref(x_43);
 x_80 = lean_box(0);
}
x_81 = 1;
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(1, 4, 1);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_42);
lean_ctor_set(x_82, 1, x_74);
lean_ctor_set(x_82, 2, x_75);
lean_ctor_set(x_82, 3, x_76);
lean_ctor_set_uint8(x_82, sizeof(void*)*4, x_81);
x_83 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_34);
lean_ctor_set(x_83, 2, x_35);
lean_ctor_set(x_83, 3, x_36);
lean_ctor_set_uint8(x_83, sizeof(void*)*4, x_81);
x_84 = 0;
lean_ctor_set(x_1, 3, x_83);
lean_ctor_set(x_1, 2, x_78);
lean_ctor_set(x_1, 1, x_77);
lean_ctor_set(x_1, 0, x_82);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_84);
return x_1;
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_41);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_41, 3);
lean_dec(x_86);
x_87 = lean_ctor_get(x_41, 0);
lean_dec(x_87);
x_88 = 0;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_88);
x_89 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_89);
return x_1;
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; uint8_t x_94; 
x_90 = lean_ctor_get(x_41, 1);
x_91 = lean_ctor_get(x_41, 2);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_41);
x_92 = 0;
x_93 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_93, 0, x_42);
lean_ctor_set(x_93, 1, x_90);
lean_ctor_set(x_93, 2, x_91);
lean_ctor_set(x_93, 3, x_43);
lean_ctor_set_uint8(x_93, sizeof(void*)*4, x_92);
x_94 = 1;
lean_ctor_set(x_1, 0, x_93);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_94);
return x_1;
}
}
}
}
else
{
uint8_t x_95; 
x_95 = lean_ctor_get_uint8(x_42, sizeof(void*)*4);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_41);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_97 = lean_ctor_get(x_41, 1);
x_98 = lean_ctor_get(x_41, 2);
x_99 = lean_ctor_get(x_41, 3);
x_100 = lean_ctor_get(x_41, 0);
lean_dec(x_100);
x_101 = !lean_is_exclusive(x_42);
if (x_101 == 0)
{
uint8_t x_102; uint8_t x_103; 
x_102 = 1;
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_102);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_99);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_102);
x_103 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_98);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_42);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_103);
return x_1;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; uint8_t x_110; 
x_104 = lean_ctor_get(x_42, 0);
x_105 = lean_ctor_get(x_42, 1);
x_106 = lean_ctor_get(x_42, 2);
x_107 = lean_ctor_get(x_42, 3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_42);
x_108 = 1;
x_109 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_109, 0, x_104);
lean_ctor_set(x_109, 1, x_105);
lean_ctor_set(x_109, 2, x_106);
lean_ctor_set(x_109, 3, x_107);
lean_ctor_set_uint8(x_109, sizeof(void*)*4, x_108);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_99);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_108);
x_110 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_98);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_109);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_110);
return x_1;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_111 = lean_ctor_get(x_41, 1);
x_112 = lean_ctor_get(x_41, 2);
x_113 = lean_ctor_get(x_41, 3);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_41);
x_114 = lean_ctor_get(x_42, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_42, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_42, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_42, 3);
lean_inc(x_117);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_118 = x_42;
} else {
 lean_dec_ref(x_42);
 x_118 = lean_box(0);
}
x_119 = 1;
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(1, 4, 1);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_114);
lean_ctor_set(x_120, 1, x_115);
lean_ctor_set(x_120, 2, x_116);
lean_ctor_set(x_120, 3, x_117);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_119);
x_121 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_121, 0, x_113);
lean_ctor_set(x_121, 1, x_34);
lean_ctor_set(x_121, 2, x_35);
lean_ctor_set(x_121, 3, x_36);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_119);
x_122 = 0;
lean_ctor_set(x_1, 3, x_121);
lean_ctor_set(x_1, 2, x_112);
lean_ctor_set(x_1, 1, x_111);
lean_ctor_set(x_1, 0, x_120);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_122);
return x_1;
}
}
else
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_41, 3);
lean_inc(x_123);
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_41);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_128; 
x_125 = lean_ctor_get(x_41, 3);
lean_dec(x_125);
x_126 = lean_ctor_get(x_41, 0);
lean_dec(x_126);
x_127 = 0;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_127);
x_128 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_128);
return x_1;
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; uint8_t x_133; 
x_129 = lean_ctor_get(x_41, 1);
x_130 = lean_ctor_get(x_41, 2);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_41);
x_131 = 0;
x_132 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_132, 0, x_42);
lean_ctor_set(x_132, 1, x_129);
lean_ctor_set(x_132, 2, x_130);
lean_ctor_set(x_132, 3, x_123);
lean_ctor_set_uint8(x_132, sizeof(void*)*4, x_131);
x_133 = 1;
lean_ctor_set(x_1, 0, x_132);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_133);
return x_1;
}
}
else
{
uint8_t x_134; 
x_134 = lean_ctor_get_uint8(x_123, sizeof(void*)*4);
if (x_134 == 0)
{
uint8_t x_135; 
lean_free_object(x_1);
x_135 = !lean_is_exclusive(x_41);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_136 = lean_ctor_get(x_41, 1);
x_137 = lean_ctor_get(x_41, 2);
x_138 = lean_ctor_get(x_41, 3);
lean_dec(x_138);
x_139 = lean_ctor_get(x_41, 0);
lean_dec(x_139);
x_140 = !lean_is_exclusive(x_123);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; uint8_t x_146; 
x_141 = lean_ctor_get(x_123, 0);
x_142 = lean_ctor_get(x_123, 1);
x_143 = lean_ctor_get(x_123, 2);
x_144 = lean_ctor_get(x_123, 3);
x_145 = 1;
lean_inc(x_42);
lean_ctor_set(x_123, 3, x_141);
lean_ctor_set(x_123, 2, x_137);
lean_ctor_set(x_123, 1, x_136);
lean_ctor_set(x_123, 0, x_42);
x_146 = !lean_is_exclusive(x_42);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_147 = lean_ctor_get(x_42, 3);
lean_dec(x_147);
x_148 = lean_ctor_get(x_42, 2);
lean_dec(x_148);
x_149 = lean_ctor_get(x_42, 1);
lean_dec(x_149);
x_150 = lean_ctor_get(x_42, 0);
lean_dec(x_150);
lean_ctor_set_uint8(x_123, sizeof(void*)*4, x_145);
lean_ctor_set(x_42, 3, x_36);
lean_ctor_set(x_42, 2, x_35);
lean_ctor_set(x_42, 1, x_34);
lean_ctor_set(x_42, 0, x_144);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_145);
x_151 = 0;
lean_ctor_set(x_41, 3, x_42);
lean_ctor_set(x_41, 2, x_143);
lean_ctor_set(x_41, 1, x_142);
lean_ctor_set(x_41, 0, x_123);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_151);
return x_41;
}
else
{
lean_object* x_152; uint8_t x_153; 
lean_dec(x_42);
lean_ctor_set_uint8(x_123, sizeof(void*)*4, x_145);
x_152 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_152, 0, x_144);
lean_ctor_set(x_152, 1, x_34);
lean_ctor_set(x_152, 2, x_35);
lean_ctor_set(x_152, 3, x_36);
lean_ctor_set_uint8(x_152, sizeof(void*)*4, x_145);
x_153 = 0;
lean_ctor_set(x_41, 3, x_152);
lean_ctor_set(x_41, 2, x_143);
lean_ctor_set(x_41, 1, x_142);
lean_ctor_set(x_41, 0, x_123);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_153);
return x_41;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_154 = lean_ctor_get(x_123, 0);
x_155 = lean_ctor_get(x_123, 1);
x_156 = lean_ctor_get(x_123, 2);
x_157 = lean_ctor_get(x_123, 3);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_123);
x_158 = 1;
lean_inc(x_42);
x_159 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_159, 0, x_42);
lean_ctor_set(x_159, 1, x_136);
lean_ctor_set(x_159, 2, x_137);
lean_ctor_set(x_159, 3, x_154);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_160 = x_42;
} else {
 lean_dec_ref(x_42);
 x_160 = lean_box(0);
}
lean_ctor_set_uint8(x_159, sizeof(void*)*4, x_158);
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 4, 1);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_157);
lean_ctor_set(x_161, 1, x_34);
lean_ctor_set(x_161, 2, x_35);
lean_ctor_set(x_161, 3, x_36);
lean_ctor_set_uint8(x_161, sizeof(void*)*4, x_158);
x_162 = 0;
lean_ctor_set(x_41, 3, x_161);
lean_ctor_set(x_41, 2, x_156);
lean_ctor_set(x_41, 1, x_155);
lean_ctor_set(x_41, 0, x_159);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_162);
return x_41;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; 
x_163 = lean_ctor_get(x_41, 1);
x_164 = lean_ctor_get(x_41, 2);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_41);
x_165 = lean_ctor_get(x_123, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_123, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_123, 2);
lean_inc(x_167);
x_168 = lean_ctor_get(x_123, 3);
lean_inc(x_168);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 x_169 = x_123;
} else {
 lean_dec_ref(x_123);
 x_169 = lean_box(0);
}
x_170 = 1;
lean_inc(x_42);
if (lean_is_scalar(x_169)) {
 x_171 = lean_alloc_ctor(1, 4, 1);
} else {
 x_171 = x_169;
}
lean_ctor_set(x_171, 0, x_42);
lean_ctor_set(x_171, 1, x_163);
lean_ctor_set(x_171, 2, x_164);
lean_ctor_set(x_171, 3, x_165);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_172 = x_42;
} else {
 lean_dec_ref(x_42);
 x_172 = lean_box(0);
}
lean_ctor_set_uint8(x_171, sizeof(void*)*4, x_170);
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 4, 1);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_168);
lean_ctor_set(x_173, 1, x_34);
lean_ctor_set(x_173, 2, x_35);
lean_ctor_set(x_173, 3, x_36);
lean_ctor_set_uint8(x_173, sizeof(void*)*4, x_170);
x_174 = 0;
x_175 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_175, 0, x_171);
lean_ctor_set(x_175, 1, x_166);
lean_ctor_set(x_175, 2, x_167);
lean_ctor_set(x_175, 3, x_173);
lean_ctor_set_uint8(x_175, sizeof(void*)*4, x_174);
return x_175;
}
}
else
{
uint8_t x_176; 
x_176 = !lean_is_exclusive(x_41);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_177 = lean_ctor_get(x_41, 3);
lean_dec(x_177);
x_178 = lean_ctor_get(x_41, 0);
lean_dec(x_178);
x_179 = !lean_is_exclusive(x_42);
if (x_179 == 0)
{
uint8_t x_180; uint8_t x_181; 
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_134);
x_180 = 0;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_180);
x_181 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_181);
return x_1;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; uint8_t x_188; 
x_182 = lean_ctor_get(x_42, 0);
x_183 = lean_ctor_get(x_42, 1);
x_184 = lean_ctor_get(x_42, 2);
x_185 = lean_ctor_get(x_42, 3);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_42);
x_186 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_186, 0, x_182);
lean_ctor_set(x_186, 1, x_183);
lean_ctor_set(x_186, 2, x_184);
lean_ctor_set(x_186, 3, x_185);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_134);
x_187 = 0;
lean_ctor_set(x_41, 0, x_186);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_187);
x_188 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; uint8_t x_199; 
x_189 = lean_ctor_get(x_41, 1);
x_190 = lean_ctor_get(x_41, 2);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_41);
x_191 = lean_ctor_get(x_42, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_42, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_42, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_42, 3);
lean_inc(x_194);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_195 = x_42;
} else {
 lean_dec_ref(x_42);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 4, 1);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_191);
lean_ctor_set(x_196, 1, x_192);
lean_ctor_set(x_196, 2, x_193);
lean_ctor_set(x_196, 3, x_194);
lean_ctor_set_uint8(x_196, sizeof(void*)*4, x_134);
x_197 = 0;
x_198 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_189);
lean_ctor_set(x_198, 2, x_190);
lean_ctor_set(x_198, 3, x_123);
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_197);
x_199 = 1;
lean_ctor_set(x_1, 0, x_198);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
}
}
}
}
}
case 1:
{
uint8_t x_200; 
lean_dec(x_35);
lean_dec(x_34);
x_200 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
default: 
{
uint8_t x_201; 
x_201 = l_Std_RBNode_isRed___rarg(x_36);
if (x_201 == 0)
{
lean_object* x_202; uint8_t x_203; 
x_202 = l_Std_RBNode_ins___at_Lean_Server_FileWorker_queueRequest___spec__2(x_36, x_2, x_3);
x_203 = 1;
lean_ctor_set(x_1, 3, x_202);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_203);
return x_1;
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = l_Std_RBNode_ins___at_Lean_Server_FileWorker_queueRequest___spec__2(x_36, x_2, x_3);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_204, 3);
lean_inc(x_206);
if (lean_obj_tag(x_206) == 0)
{
uint8_t x_207; 
x_207 = !lean_is_exclusive(x_204);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; uint8_t x_211; 
x_208 = lean_ctor_get(x_204, 3);
lean_dec(x_208);
x_209 = lean_ctor_get(x_204, 0);
lean_dec(x_209);
x_210 = 0;
lean_ctor_set(x_204, 0, x_206);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_210);
x_211 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_211);
return x_1;
}
else
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; uint8_t x_216; 
x_212 = lean_ctor_get(x_204, 1);
x_213 = lean_ctor_get(x_204, 2);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_204);
x_214 = 0;
x_215 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_215, 0, x_206);
lean_ctor_set(x_215, 1, x_212);
lean_ctor_set(x_215, 2, x_213);
lean_ctor_set(x_215, 3, x_206);
lean_ctor_set_uint8(x_215, sizeof(void*)*4, x_214);
x_216 = 1;
lean_ctor_set(x_1, 3, x_215);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_216);
return x_1;
}
}
else
{
uint8_t x_217; 
x_217 = lean_ctor_get_uint8(x_206, sizeof(void*)*4);
if (x_217 == 0)
{
uint8_t x_218; 
x_218 = !lean_is_exclusive(x_204);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_219 = lean_ctor_get(x_204, 1);
x_220 = lean_ctor_get(x_204, 2);
x_221 = lean_ctor_get(x_204, 3);
lean_dec(x_221);
x_222 = lean_ctor_get(x_204, 0);
lean_dec(x_222);
x_223 = !lean_is_exclusive(x_206);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; uint8_t x_229; 
x_224 = lean_ctor_get(x_206, 0);
x_225 = lean_ctor_get(x_206, 1);
x_226 = lean_ctor_get(x_206, 2);
x_227 = lean_ctor_get(x_206, 3);
x_228 = 1;
lean_ctor_set(x_206, 3, x_205);
lean_ctor_set(x_206, 2, x_35);
lean_ctor_set(x_206, 1, x_34);
lean_ctor_set(x_206, 0, x_33);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_228);
lean_ctor_set(x_204, 3, x_227);
lean_ctor_set(x_204, 2, x_226);
lean_ctor_set(x_204, 1, x_225);
lean_ctor_set(x_204, 0, x_224);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_228);
x_229 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_220);
lean_ctor_set(x_1, 1, x_219);
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_229);
return x_1;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; uint8_t x_236; 
x_230 = lean_ctor_get(x_206, 0);
x_231 = lean_ctor_get(x_206, 1);
x_232 = lean_ctor_get(x_206, 2);
x_233 = lean_ctor_get(x_206, 3);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_206);
x_234 = 1;
x_235 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_235, 0, x_33);
lean_ctor_set(x_235, 1, x_34);
lean_ctor_set(x_235, 2, x_35);
lean_ctor_set(x_235, 3, x_205);
lean_ctor_set_uint8(x_235, sizeof(void*)*4, x_234);
lean_ctor_set(x_204, 3, x_233);
lean_ctor_set(x_204, 2, x_232);
lean_ctor_set(x_204, 1, x_231);
lean_ctor_set(x_204, 0, x_230);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_234);
x_236 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_220);
lean_ctor_set(x_1, 1, x_219);
lean_ctor_set(x_1, 0, x_235);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_236);
return x_1;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_237 = lean_ctor_get(x_204, 1);
x_238 = lean_ctor_get(x_204, 2);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_204);
x_239 = lean_ctor_get(x_206, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_206, 1);
lean_inc(x_240);
x_241 = lean_ctor_get(x_206, 2);
lean_inc(x_241);
x_242 = lean_ctor_get(x_206, 3);
lean_inc(x_242);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 lean_ctor_release(x_206, 2);
 lean_ctor_release(x_206, 3);
 x_243 = x_206;
} else {
 lean_dec_ref(x_206);
 x_243 = lean_box(0);
}
x_244 = 1;
if (lean_is_scalar(x_243)) {
 x_245 = lean_alloc_ctor(1, 4, 1);
} else {
 x_245 = x_243;
}
lean_ctor_set(x_245, 0, x_33);
lean_ctor_set(x_245, 1, x_34);
lean_ctor_set(x_245, 2, x_35);
lean_ctor_set(x_245, 3, x_205);
lean_ctor_set_uint8(x_245, sizeof(void*)*4, x_244);
x_246 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_246, 0, x_239);
lean_ctor_set(x_246, 1, x_240);
lean_ctor_set(x_246, 2, x_241);
lean_ctor_set(x_246, 3, x_242);
lean_ctor_set_uint8(x_246, sizeof(void*)*4, x_244);
x_247 = 0;
lean_ctor_set(x_1, 3, x_246);
lean_ctor_set(x_1, 2, x_238);
lean_ctor_set(x_1, 1, x_237);
lean_ctor_set(x_1, 0, x_245);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_247);
return x_1;
}
}
else
{
uint8_t x_248; 
x_248 = !lean_is_exclusive(x_204);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; uint8_t x_251; uint8_t x_252; 
x_249 = lean_ctor_get(x_204, 3);
lean_dec(x_249);
x_250 = lean_ctor_get(x_204, 0);
lean_dec(x_250);
x_251 = 0;
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_251);
x_252 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_252);
return x_1;
}
else
{
lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; uint8_t x_257; 
x_253 = lean_ctor_get(x_204, 1);
x_254 = lean_ctor_get(x_204, 2);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_204);
x_255 = 0;
x_256 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_256, 0, x_205);
lean_ctor_set(x_256, 1, x_253);
lean_ctor_set(x_256, 2, x_254);
lean_ctor_set(x_256, 3, x_206);
lean_ctor_set_uint8(x_256, sizeof(void*)*4, x_255);
x_257 = 1;
lean_ctor_set(x_1, 3, x_256);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_257);
return x_1;
}
}
}
}
else
{
uint8_t x_258; 
x_258 = lean_ctor_get_uint8(x_205, sizeof(void*)*4);
if (x_258 == 0)
{
uint8_t x_259; 
x_259 = !lean_is_exclusive(x_204);
if (x_259 == 0)
{
lean_object* x_260; uint8_t x_261; 
x_260 = lean_ctor_get(x_204, 0);
lean_dec(x_260);
x_261 = !lean_is_exclusive(x_205);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; uint8_t x_267; 
x_262 = lean_ctor_get(x_205, 0);
x_263 = lean_ctor_get(x_205, 1);
x_264 = lean_ctor_get(x_205, 2);
x_265 = lean_ctor_get(x_205, 3);
x_266 = 1;
lean_ctor_set(x_205, 3, x_262);
lean_ctor_set(x_205, 2, x_35);
lean_ctor_set(x_205, 1, x_34);
lean_ctor_set(x_205, 0, x_33);
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_266);
lean_ctor_set(x_204, 0, x_265);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_266);
x_267 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_264);
lean_ctor_set(x_1, 1, x_263);
lean_ctor_set(x_1, 0, x_205);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_267);
return x_1;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; lean_object* x_273; uint8_t x_274; 
x_268 = lean_ctor_get(x_205, 0);
x_269 = lean_ctor_get(x_205, 1);
x_270 = lean_ctor_get(x_205, 2);
x_271 = lean_ctor_get(x_205, 3);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_205);
x_272 = 1;
x_273 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_273, 0, x_33);
lean_ctor_set(x_273, 1, x_34);
lean_ctor_set(x_273, 2, x_35);
lean_ctor_set(x_273, 3, x_268);
lean_ctor_set_uint8(x_273, sizeof(void*)*4, x_272);
lean_ctor_set(x_204, 0, x_271);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_272);
x_274 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_270);
lean_ctor_set(x_1, 1, x_269);
lean_ctor_set(x_1, 0, x_273);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_274);
return x_1;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_275 = lean_ctor_get(x_204, 1);
x_276 = lean_ctor_get(x_204, 2);
x_277 = lean_ctor_get(x_204, 3);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_204);
x_278 = lean_ctor_get(x_205, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_205, 1);
lean_inc(x_279);
x_280 = lean_ctor_get(x_205, 2);
lean_inc(x_280);
x_281 = lean_ctor_get(x_205, 3);
lean_inc(x_281);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_282 = x_205;
} else {
 lean_dec_ref(x_205);
 x_282 = lean_box(0);
}
x_283 = 1;
if (lean_is_scalar(x_282)) {
 x_284 = lean_alloc_ctor(1, 4, 1);
} else {
 x_284 = x_282;
}
lean_ctor_set(x_284, 0, x_33);
lean_ctor_set(x_284, 1, x_34);
lean_ctor_set(x_284, 2, x_35);
lean_ctor_set(x_284, 3, x_278);
lean_ctor_set_uint8(x_284, sizeof(void*)*4, x_283);
x_285 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_285, 0, x_281);
lean_ctor_set(x_285, 1, x_275);
lean_ctor_set(x_285, 2, x_276);
lean_ctor_set(x_285, 3, x_277);
lean_ctor_set_uint8(x_285, sizeof(void*)*4, x_283);
x_286 = 0;
lean_ctor_set(x_1, 3, x_285);
lean_ctor_set(x_1, 2, x_280);
lean_ctor_set(x_1, 1, x_279);
lean_ctor_set(x_1, 0, x_284);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_286);
return x_1;
}
}
else
{
lean_object* x_287; 
x_287 = lean_ctor_get(x_204, 3);
lean_inc(x_287);
if (lean_obj_tag(x_287) == 0)
{
uint8_t x_288; 
x_288 = !lean_is_exclusive(x_204);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; uint8_t x_291; uint8_t x_292; 
x_289 = lean_ctor_get(x_204, 3);
lean_dec(x_289);
x_290 = lean_ctor_get(x_204, 0);
lean_dec(x_290);
x_291 = 0;
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_291);
x_292 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_292);
return x_1;
}
else
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; lean_object* x_296; uint8_t x_297; 
x_293 = lean_ctor_get(x_204, 1);
x_294 = lean_ctor_get(x_204, 2);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_204);
x_295 = 0;
x_296 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_296, 0, x_205);
lean_ctor_set(x_296, 1, x_293);
lean_ctor_set(x_296, 2, x_294);
lean_ctor_set(x_296, 3, x_287);
lean_ctor_set_uint8(x_296, sizeof(void*)*4, x_295);
x_297 = 1;
lean_ctor_set(x_1, 3, x_296);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_297);
return x_1;
}
}
else
{
uint8_t x_298; 
x_298 = lean_ctor_get_uint8(x_287, sizeof(void*)*4);
if (x_298 == 0)
{
uint8_t x_299; 
lean_free_object(x_1);
x_299 = !lean_is_exclusive(x_204);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; uint8_t x_302; 
x_300 = lean_ctor_get(x_204, 3);
lean_dec(x_300);
x_301 = lean_ctor_get(x_204, 0);
lean_dec(x_301);
x_302 = !lean_is_exclusive(x_287);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; uint8_t x_308; 
x_303 = lean_ctor_get(x_287, 0);
x_304 = lean_ctor_get(x_287, 1);
x_305 = lean_ctor_get(x_287, 2);
x_306 = lean_ctor_get(x_287, 3);
x_307 = 1;
lean_inc(x_205);
lean_ctor_set(x_287, 3, x_205);
lean_ctor_set(x_287, 2, x_35);
lean_ctor_set(x_287, 1, x_34);
lean_ctor_set(x_287, 0, x_33);
x_308 = !lean_is_exclusive(x_205);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; 
x_309 = lean_ctor_get(x_205, 3);
lean_dec(x_309);
x_310 = lean_ctor_get(x_205, 2);
lean_dec(x_310);
x_311 = lean_ctor_get(x_205, 1);
lean_dec(x_311);
x_312 = lean_ctor_get(x_205, 0);
lean_dec(x_312);
lean_ctor_set_uint8(x_287, sizeof(void*)*4, x_307);
lean_ctor_set(x_205, 3, x_306);
lean_ctor_set(x_205, 2, x_305);
lean_ctor_set(x_205, 1, x_304);
lean_ctor_set(x_205, 0, x_303);
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_307);
x_313 = 0;
lean_ctor_set(x_204, 3, x_205);
lean_ctor_set(x_204, 0, x_287);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_313);
return x_204;
}
else
{
lean_object* x_314; uint8_t x_315; 
lean_dec(x_205);
lean_ctor_set_uint8(x_287, sizeof(void*)*4, x_307);
x_314 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_314, 0, x_303);
lean_ctor_set(x_314, 1, x_304);
lean_ctor_set(x_314, 2, x_305);
lean_ctor_set(x_314, 3, x_306);
lean_ctor_set_uint8(x_314, sizeof(void*)*4, x_307);
x_315 = 0;
lean_ctor_set(x_204, 3, x_314);
lean_ctor_set(x_204, 0, x_287);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_315);
return x_204;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_316 = lean_ctor_get(x_287, 0);
x_317 = lean_ctor_get(x_287, 1);
x_318 = lean_ctor_get(x_287, 2);
x_319 = lean_ctor_get(x_287, 3);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_287);
x_320 = 1;
lean_inc(x_205);
x_321 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_321, 0, x_33);
lean_ctor_set(x_321, 1, x_34);
lean_ctor_set(x_321, 2, x_35);
lean_ctor_set(x_321, 3, x_205);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_322 = x_205;
} else {
 lean_dec_ref(x_205);
 x_322 = lean_box(0);
}
lean_ctor_set_uint8(x_321, sizeof(void*)*4, x_320);
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 4, 1);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_316);
lean_ctor_set(x_323, 1, x_317);
lean_ctor_set(x_323, 2, x_318);
lean_ctor_set(x_323, 3, x_319);
lean_ctor_set_uint8(x_323, sizeof(void*)*4, x_320);
x_324 = 0;
lean_ctor_set(x_204, 3, x_323);
lean_ctor_set(x_204, 0, x_321);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_324);
return x_204;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; lean_object* x_337; 
x_325 = lean_ctor_get(x_204, 1);
x_326 = lean_ctor_get(x_204, 2);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_204);
x_327 = lean_ctor_get(x_287, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_287, 1);
lean_inc(x_328);
x_329 = lean_ctor_get(x_287, 2);
lean_inc(x_329);
x_330 = lean_ctor_get(x_287, 3);
lean_inc(x_330);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 lean_ctor_release(x_287, 2);
 lean_ctor_release(x_287, 3);
 x_331 = x_287;
} else {
 lean_dec_ref(x_287);
 x_331 = lean_box(0);
}
x_332 = 1;
lean_inc(x_205);
if (lean_is_scalar(x_331)) {
 x_333 = lean_alloc_ctor(1, 4, 1);
} else {
 x_333 = x_331;
}
lean_ctor_set(x_333, 0, x_33);
lean_ctor_set(x_333, 1, x_34);
lean_ctor_set(x_333, 2, x_35);
lean_ctor_set(x_333, 3, x_205);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_334 = x_205;
} else {
 lean_dec_ref(x_205);
 x_334 = lean_box(0);
}
lean_ctor_set_uint8(x_333, sizeof(void*)*4, x_332);
if (lean_is_scalar(x_334)) {
 x_335 = lean_alloc_ctor(1, 4, 1);
} else {
 x_335 = x_334;
}
lean_ctor_set(x_335, 0, x_327);
lean_ctor_set(x_335, 1, x_328);
lean_ctor_set(x_335, 2, x_329);
lean_ctor_set(x_335, 3, x_330);
lean_ctor_set_uint8(x_335, sizeof(void*)*4, x_332);
x_336 = 0;
x_337 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_337, 0, x_333);
lean_ctor_set(x_337, 1, x_325);
lean_ctor_set(x_337, 2, x_326);
lean_ctor_set(x_337, 3, x_335);
lean_ctor_set_uint8(x_337, sizeof(void*)*4, x_336);
return x_337;
}
}
else
{
uint8_t x_338; 
x_338 = !lean_is_exclusive(x_204);
if (x_338 == 0)
{
lean_object* x_339; lean_object* x_340; uint8_t x_341; 
x_339 = lean_ctor_get(x_204, 3);
lean_dec(x_339);
x_340 = lean_ctor_get(x_204, 0);
lean_dec(x_340);
x_341 = !lean_is_exclusive(x_205);
if (x_341 == 0)
{
uint8_t x_342; uint8_t x_343; 
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_298);
x_342 = 0;
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_342);
x_343 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_343);
return x_1;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; uint8_t x_350; 
x_344 = lean_ctor_get(x_205, 0);
x_345 = lean_ctor_get(x_205, 1);
x_346 = lean_ctor_get(x_205, 2);
x_347 = lean_ctor_get(x_205, 3);
lean_inc(x_347);
lean_inc(x_346);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_205);
x_348 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_348, 0, x_344);
lean_ctor_set(x_348, 1, x_345);
lean_ctor_set(x_348, 2, x_346);
lean_ctor_set(x_348, 3, x_347);
lean_ctor_set_uint8(x_348, sizeof(void*)*4, x_298);
x_349 = 0;
lean_ctor_set(x_204, 0, x_348);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_349);
x_350 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_350);
return x_1;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; uint8_t x_361; 
x_351 = lean_ctor_get(x_204, 1);
x_352 = lean_ctor_get(x_204, 2);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_204);
x_353 = lean_ctor_get(x_205, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_205, 1);
lean_inc(x_354);
x_355 = lean_ctor_get(x_205, 2);
lean_inc(x_355);
x_356 = lean_ctor_get(x_205, 3);
lean_inc(x_356);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_357 = x_205;
} else {
 lean_dec_ref(x_205);
 x_357 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_358 = lean_alloc_ctor(1, 4, 1);
} else {
 x_358 = x_357;
}
lean_ctor_set(x_358, 0, x_353);
lean_ctor_set(x_358, 1, x_354);
lean_ctor_set(x_358, 2, x_355);
lean_ctor_set(x_358, 3, x_356);
lean_ctor_set_uint8(x_358, sizeof(void*)*4, x_298);
x_359 = 0;
x_360 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_351);
lean_ctor_set(x_360, 2, x_352);
lean_ctor_set(x_360, 3, x_287);
lean_ctor_set_uint8(x_360, sizeof(void*)*4, x_359);
x_361 = 1;
lean_ctor_set(x_1, 3, x_360);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_361);
return x_1;
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; 
x_362 = lean_ctor_get(x_1, 0);
x_363 = lean_ctor_get(x_1, 1);
x_364 = lean_ctor_get(x_1, 2);
x_365 = lean_ctor_get(x_1, 3);
lean_inc(x_365);
lean_inc(x_364);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_1);
lean_inc(x_363);
lean_inc(x_2);
x_366 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_118_(x_2, x_363);
switch (x_366) {
case 0:
{
uint8_t x_367; 
x_367 = l_Std_RBNode_isRed___rarg(x_362);
if (x_367 == 0)
{
lean_object* x_368; uint8_t x_369; lean_object* x_370; 
x_368 = l_Std_RBNode_ins___at_Lean_Server_FileWorker_queueRequest___spec__2(x_362, x_2, x_3);
x_369 = 1;
x_370 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_363);
lean_ctor_set(x_370, 2, x_364);
lean_ctor_set(x_370, 3, x_365);
lean_ctor_set_uint8(x_370, sizeof(void*)*4, x_369);
return x_370;
}
else
{
lean_object* x_371; lean_object* x_372; 
x_371 = l_Std_RBNode_ins___at_Lean_Server_FileWorker_queueRequest___spec__2(x_362, x_2, x_3);
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; 
x_373 = lean_ctor_get(x_371, 3);
lean_inc(x_373);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; lean_object* x_378; uint8_t x_379; lean_object* x_380; 
x_374 = lean_ctor_get(x_371, 1);
lean_inc(x_374);
x_375 = lean_ctor_get(x_371, 2);
lean_inc(x_375);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_376 = x_371;
} else {
 lean_dec_ref(x_371);
 x_376 = lean_box(0);
}
x_377 = 0;
if (lean_is_scalar(x_376)) {
 x_378 = lean_alloc_ctor(1, 4, 1);
} else {
 x_378 = x_376;
}
lean_ctor_set(x_378, 0, x_373);
lean_ctor_set(x_378, 1, x_374);
lean_ctor_set(x_378, 2, x_375);
lean_ctor_set(x_378, 3, x_373);
lean_ctor_set_uint8(x_378, sizeof(void*)*4, x_377);
x_379 = 1;
x_380 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_363);
lean_ctor_set(x_380, 2, x_364);
lean_ctor_set(x_380, 3, x_365);
lean_ctor_set_uint8(x_380, sizeof(void*)*4, x_379);
return x_380;
}
else
{
uint8_t x_381; 
x_381 = lean_ctor_get_uint8(x_373, sizeof(void*)*4);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; uint8_t x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; lean_object* x_394; 
x_382 = lean_ctor_get(x_371, 1);
lean_inc(x_382);
x_383 = lean_ctor_get(x_371, 2);
lean_inc(x_383);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_384 = x_371;
} else {
 lean_dec_ref(x_371);
 x_384 = lean_box(0);
}
x_385 = lean_ctor_get(x_373, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_373, 1);
lean_inc(x_386);
x_387 = lean_ctor_get(x_373, 2);
lean_inc(x_387);
x_388 = lean_ctor_get(x_373, 3);
lean_inc(x_388);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 lean_ctor_release(x_373, 2);
 lean_ctor_release(x_373, 3);
 x_389 = x_373;
} else {
 lean_dec_ref(x_373);
 x_389 = lean_box(0);
}
x_390 = 1;
if (lean_is_scalar(x_389)) {
 x_391 = lean_alloc_ctor(1, 4, 1);
} else {
 x_391 = x_389;
}
lean_ctor_set(x_391, 0, x_372);
lean_ctor_set(x_391, 1, x_382);
lean_ctor_set(x_391, 2, x_383);
lean_ctor_set(x_391, 3, x_385);
lean_ctor_set_uint8(x_391, sizeof(void*)*4, x_390);
if (lean_is_scalar(x_384)) {
 x_392 = lean_alloc_ctor(1, 4, 1);
} else {
 x_392 = x_384;
}
lean_ctor_set(x_392, 0, x_388);
lean_ctor_set(x_392, 1, x_363);
lean_ctor_set(x_392, 2, x_364);
lean_ctor_set(x_392, 3, x_365);
lean_ctor_set_uint8(x_392, sizeof(void*)*4, x_390);
x_393 = 0;
x_394 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_394, 0, x_391);
lean_ctor_set(x_394, 1, x_386);
lean_ctor_set(x_394, 2, x_387);
lean_ctor_set(x_394, 3, x_392);
lean_ctor_set_uint8(x_394, sizeof(void*)*4, x_393);
return x_394;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; lean_object* x_399; uint8_t x_400; lean_object* x_401; 
x_395 = lean_ctor_get(x_371, 1);
lean_inc(x_395);
x_396 = lean_ctor_get(x_371, 2);
lean_inc(x_396);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_397 = x_371;
} else {
 lean_dec_ref(x_371);
 x_397 = lean_box(0);
}
x_398 = 0;
if (lean_is_scalar(x_397)) {
 x_399 = lean_alloc_ctor(1, 4, 1);
} else {
 x_399 = x_397;
}
lean_ctor_set(x_399, 0, x_372);
lean_ctor_set(x_399, 1, x_395);
lean_ctor_set(x_399, 2, x_396);
lean_ctor_set(x_399, 3, x_373);
lean_ctor_set_uint8(x_399, sizeof(void*)*4, x_398);
x_400 = 1;
x_401 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_401, 0, x_399);
lean_ctor_set(x_401, 1, x_363);
lean_ctor_set(x_401, 2, x_364);
lean_ctor_set(x_401, 3, x_365);
lean_ctor_set_uint8(x_401, sizeof(void*)*4, x_400);
return x_401;
}
}
}
else
{
uint8_t x_402; 
x_402 = lean_ctor_get_uint8(x_372, sizeof(void*)*4);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; lean_object* x_416; 
x_403 = lean_ctor_get(x_371, 1);
lean_inc(x_403);
x_404 = lean_ctor_get(x_371, 2);
lean_inc(x_404);
x_405 = lean_ctor_get(x_371, 3);
lean_inc(x_405);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_406 = x_371;
} else {
 lean_dec_ref(x_371);
 x_406 = lean_box(0);
}
x_407 = lean_ctor_get(x_372, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_372, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_372, 2);
lean_inc(x_409);
x_410 = lean_ctor_get(x_372, 3);
lean_inc(x_410);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 lean_ctor_release(x_372, 3);
 x_411 = x_372;
} else {
 lean_dec_ref(x_372);
 x_411 = lean_box(0);
}
x_412 = 1;
if (lean_is_scalar(x_411)) {
 x_413 = lean_alloc_ctor(1, 4, 1);
} else {
 x_413 = x_411;
}
lean_ctor_set(x_413, 0, x_407);
lean_ctor_set(x_413, 1, x_408);
lean_ctor_set(x_413, 2, x_409);
lean_ctor_set(x_413, 3, x_410);
lean_ctor_set_uint8(x_413, sizeof(void*)*4, x_412);
if (lean_is_scalar(x_406)) {
 x_414 = lean_alloc_ctor(1, 4, 1);
} else {
 x_414 = x_406;
}
lean_ctor_set(x_414, 0, x_405);
lean_ctor_set(x_414, 1, x_363);
lean_ctor_set(x_414, 2, x_364);
lean_ctor_set(x_414, 3, x_365);
lean_ctor_set_uint8(x_414, sizeof(void*)*4, x_412);
x_415 = 0;
x_416 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_416, 0, x_413);
lean_ctor_set(x_416, 1, x_403);
lean_ctor_set(x_416, 2, x_404);
lean_ctor_set(x_416, 3, x_414);
lean_ctor_set_uint8(x_416, sizeof(void*)*4, x_415);
return x_416;
}
else
{
lean_object* x_417; 
x_417 = lean_ctor_get(x_371, 3);
lean_inc(x_417);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; uint8_t x_423; lean_object* x_424; 
x_418 = lean_ctor_get(x_371, 1);
lean_inc(x_418);
x_419 = lean_ctor_get(x_371, 2);
lean_inc(x_419);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_420 = x_371;
} else {
 lean_dec_ref(x_371);
 x_420 = lean_box(0);
}
x_421 = 0;
if (lean_is_scalar(x_420)) {
 x_422 = lean_alloc_ctor(1, 4, 1);
} else {
 x_422 = x_420;
}
lean_ctor_set(x_422, 0, x_372);
lean_ctor_set(x_422, 1, x_418);
lean_ctor_set(x_422, 2, x_419);
lean_ctor_set(x_422, 3, x_417);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_421);
x_423 = 1;
x_424 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_363);
lean_ctor_set(x_424, 2, x_364);
lean_ctor_set(x_424, 3, x_365);
lean_ctor_set_uint8(x_424, sizeof(void*)*4, x_423);
return x_424;
}
else
{
uint8_t x_425; 
x_425 = lean_ctor_get_uint8(x_417, sizeof(void*)*4);
if (x_425 == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; 
x_426 = lean_ctor_get(x_371, 1);
lean_inc(x_426);
x_427 = lean_ctor_get(x_371, 2);
lean_inc(x_427);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_428 = x_371;
} else {
 lean_dec_ref(x_371);
 x_428 = lean_box(0);
}
x_429 = lean_ctor_get(x_417, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_417, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_417, 2);
lean_inc(x_431);
x_432 = lean_ctor_get(x_417, 3);
lean_inc(x_432);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 x_433 = x_417;
} else {
 lean_dec_ref(x_417);
 x_433 = lean_box(0);
}
x_434 = 1;
lean_inc(x_372);
if (lean_is_scalar(x_433)) {
 x_435 = lean_alloc_ctor(1, 4, 1);
} else {
 x_435 = x_433;
}
lean_ctor_set(x_435, 0, x_372);
lean_ctor_set(x_435, 1, x_426);
lean_ctor_set(x_435, 2, x_427);
lean_ctor_set(x_435, 3, x_429);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 lean_ctor_release(x_372, 3);
 x_436 = x_372;
} else {
 lean_dec_ref(x_372);
 x_436 = lean_box(0);
}
lean_ctor_set_uint8(x_435, sizeof(void*)*4, x_434);
if (lean_is_scalar(x_436)) {
 x_437 = lean_alloc_ctor(1, 4, 1);
} else {
 x_437 = x_436;
}
lean_ctor_set(x_437, 0, x_432);
lean_ctor_set(x_437, 1, x_363);
lean_ctor_set(x_437, 2, x_364);
lean_ctor_set(x_437, 3, x_365);
lean_ctor_set_uint8(x_437, sizeof(void*)*4, x_434);
x_438 = 0;
if (lean_is_scalar(x_428)) {
 x_439 = lean_alloc_ctor(1, 4, 1);
} else {
 x_439 = x_428;
}
lean_ctor_set(x_439, 0, x_435);
lean_ctor_set(x_439, 1, x_430);
lean_ctor_set(x_439, 2, x_431);
lean_ctor_set(x_439, 3, x_437);
lean_ctor_set_uint8(x_439, sizeof(void*)*4, x_438);
return x_439;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; uint8_t x_449; lean_object* x_450; uint8_t x_451; lean_object* x_452; 
x_440 = lean_ctor_get(x_371, 1);
lean_inc(x_440);
x_441 = lean_ctor_get(x_371, 2);
lean_inc(x_441);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_442 = x_371;
} else {
 lean_dec_ref(x_371);
 x_442 = lean_box(0);
}
x_443 = lean_ctor_get(x_372, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_372, 1);
lean_inc(x_444);
x_445 = lean_ctor_get(x_372, 2);
lean_inc(x_445);
x_446 = lean_ctor_get(x_372, 3);
lean_inc(x_446);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 lean_ctor_release(x_372, 3);
 x_447 = x_372;
} else {
 lean_dec_ref(x_372);
 x_447 = lean_box(0);
}
if (lean_is_scalar(x_447)) {
 x_448 = lean_alloc_ctor(1, 4, 1);
} else {
 x_448 = x_447;
}
lean_ctor_set(x_448, 0, x_443);
lean_ctor_set(x_448, 1, x_444);
lean_ctor_set(x_448, 2, x_445);
lean_ctor_set(x_448, 3, x_446);
lean_ctor_set_uint8(x_448, sizeof(void*)*4, x_425);
x_449 = 0;
if (lean_is_scalar(x_442)) {
 x_450 = lean_alloc_ctor(1, 4, 1);
} else {
 x_450 = x_442;
}
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_440);
lean_ctor_set(x_450, 2, x_441);
lean_ctor_set(x_450, 3, x_417);
lean_ctor_set_uint8(x_450, sizeof(void*)*4, x_449);
x_451 = 1;
x_452 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_452, 0, x_450);
lean_ctor_set(x_452, 1, x_363);
lean_ctor_set(x_452, 2, x_364);
lean_ctor_set(x_452, 3, x_365);
lean_ctor_set_uint8(x_452, sizeof(void*)*4, x_451);
return x_452;
}
}
}
}
}
}
case 1:
{
uint8_t x_453; lean_object* x_454; 
lean_dec(x_364);
lean_dec(x_363);
x_453 = 1;
x_454 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_454, 0, x_362);
lean_ctor_set(x_454, 1, x_2);
lean_ctor_set(x_454, 2, x_3);
lean_ctor_set(x_454, 3, x_365);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_453);
return x_454;
}
default: 
{
uint8_t x_455; 
x_455 = l_Std_RBNode_isRed___rarg(x_365);
if (x_455 == 0)
{
lean_object* x_456; uint8_t x_457; lean_object* x_458; 
x_456 = l_Std_RBNode_ins___at_Lean_Server_FileWorker_queueRequest___spec__2(x_365, x_2, x_3);
x_457 = 1;
x_458 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_458, 0, x_362);
lean_ctor_set(x_458, 1, x_363);
lean_ctor_set(x_458, 2, x_364);
lean_ctor_set(x_458, 3, x_456);
lean_ctor_set_uint8(x_458, sizeof(void*)*4, x_457);
return x_458;
}
else
{
lean_object* x_459; lean_object* x_460; 
x_459 = l_Std_RBNode_ins___at_Lean_Server_FileWorker_queueRequest___spec__2(x_365, x_2, x_3);
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; 
x_461 = lean_ctor_get(x_459, 3);
lean_inc(x_461);
if (lean_obj_tag(x_461) == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; lean_object* x_466; uint8_t x_467; lean_object* x_468; 
x_462 = lean_ctor_get(x_459, 1);
lean_inc(x_462);
x_463 = lean_ctor_get(x_459, 2);
lean_inc(x_463);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_464 = x_459;
} else {
 lean_dec_ref(x_459);
 x_464 = lean_box(0);
}
x_465 = 0;
if (lean_is_scalar(x_464)) {
 x_466 = lean_alloc_ctor(1, 4, 1);
} else {
 x_466 = x_464;
}
lean_ctor_set(x_466, 0, x_461);
lean_ctor_set(x_466, 1, x_462);
lean_ctor_set(x_466, 2, x_463);
lean_ctor_set(x_466, 3, x_461);
lean_ctor_set_uint8(x_466, sizeof(void*)*4, x_465);
x_467 = 1;
x_468 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_468, 0, x_362);
lean_ctor_set(x_468, 1, x_363);
lean_ctor_set(x_468, 2, x_364);
lean_ctor_set(x_468, 3, x_466);
lean_ctor_set_uint8(x_468, sizeof(void*)*4, x_467);
return x_468;
}
else
{
uint8_t x_469; 
x_469 = lean_ctor_get_uint8(x_461, sizeof(void*)*4);
if (x_469 == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; uint8_t x_478; lean_object* x_479; lean_object* x_480; uint8_t x_481; lean_object* x_482; 
x_470 = lean_ctor_get(x_459, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_459, 2);
lean_inc(x_471);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_472 = x_459;
} else {
 lean_dec_ref(x_459);
 x_472 = lean_box(0);
}
x_473 = lean_ctor_get(x_461, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_461, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_461, 2);
lean_inc(x_475);
x_476 = lean_ctor_get(x_461, 3);
lean_inc(x_476);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 lean_ctor_release(x_461, 1);
 lean_ctor_release(x_461, 2);
 lean_ctor_release(x_461, 3);
 x_477 = x_461;
} else {
 lean_dec_ref(x_461);
 x_477 = lean_box(0);
}
x_478 = 1;
if (lean_is_scalar(x_477)) {
 x_479 = lean_alloc_ctor(1, 4, 1);
} else {
 x_479 = x_477;
}
lean_ctor_set(x_479, 0, x_362);
lean_ctor_set(x_479, 1, x_363);
lean_ctor_set(x_479, 2, x_364);
lean_ctor_set(x_479, 3, x_460);
lean_ctor_set_uint8(x_479, sizeof(void*)*4, x_478);
if (lean_is_scalar(x_472)) {
 x_480 = lean_alloc_ctor(1, 4, 1);
} else {
 x_480 = x_472;
}
lean_ctor_set(x_480, 0, x_473);
lean_ctor_set(x_480, 1, x_474);
lean_ctor_set(x_480, 2, x_475);
lean_ctor_set(x_480, 3, x_476);
lean_ctor_set_uint8(x_480, sizeof(void*)*4, x_478);
x_481 = 0;
x_482 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_482, 0, x_479);
lean_ctor_set(x_482, 1, x_470);
lean_ctor_set(x_482, 2, x_471);
lean_ctor_set(x_482, 3, x_480);
lean_ctor_set_uint8(x_482, sizeof(void*)*4, x_481);
return x_482;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; uint8_t x_486; lean_object* x_487; uint8_t x_488; lean_object* x_489; 
x_483 = lean_ctor_get(x_459, 1);
lean_inc(x_483);
x_484 = lean_ctor_get(x_459, 2);
lean_inc(x_484);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_485 = x_459;
} else {
 lean_dec_ref(x_459);
 x_485 = lean_box(0);
}
x_486 = 0;
if (lean_is_scalar(x_485)) {
 x_487 = lean_alloc_ctor(1, 4, 1);
} else {
 x_487 = x_485;
}
lean_ctor_set(x_487, 0, x_460);
lean_ctor_set(x_487, 1, x_483);
lean_ctor_set(x_487, 2, x_484);
lean_ctor_set(x_487, 3, x_461);
lean_ctor_set_uint8(x_487, sizeof(void*)*4, x_486);
x_488 = 1;
x_489 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_489, 0, x_362);
lean_ctor_set(x_489, 1, x_363);
lean_ctor_set(x_489, 2, x_364);
lean_ctor_set(x_489, 3, x_487);
lean_ctor_set_uint8(x_489, sizeof(void*)*4, x_488);
return x_489;
}
}
}
else
{
uint8_t x_490; 
x_490 = lean_ctor_get_uint8(x_460, sizeof(void*)*4);
if (x_490 == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_500; lean_object* x_501; lean_object* x_502; uint8_t x_503; lean_object* x_504; 
x_491 = lean_ctor_get(x_459, 1);
lean_inc(x_491);
x_492 = lean_ctor_get(x_459, 2);
lean_inc(x_492);
x_493 = lean_ctor_get(x_459, 3);
lean_inc(x_493);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_494 = x_459;
} else {
 lean_dec_ref(x_459);
 x_494 = lean_box(0);
}
x_495 = lean_ctor_get(x_460, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_460, 1);
lean_inc(x_496);
x_497 = lean_ctor_get(x_460, 2);
lean_inc(x_497);
x_498 = lean_ctor_get(x_460, 3);
lean_inc(x_498);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 lean_ctor_release(x_460, 3);
 x_499 = x_460;
} else {
 lean_dec_ref(x_460);
 x_499 = lean_box(0);
}
x_500 = 1;
if (lean_is_scalar(x_499)) {
 x_501 = lean_alloc_ctor(1, 4, 1);
} else {
 x_501 = x_499;
}
lean_ctor_set(x_501, 0, x_362);
lean_ctor_set(x_501, 1, x_363);
lean_ctor_set(x_501, 2, x_364);
lean_ctor_set(x_501, 3, x_495);
lean_ctor_set_uint8(x_501, sizeof(void*)*4, x_500);
if (lean_is_scalar(x_494)) {
 x_502 = lean_alloc_ctor(1, 4, 1);
} else {
 x_502 = x_494;
}
lean_ctor_set(x_502, 0, x_498);
lean_ctor_set(x_502, 1, x_491);
lean_ctor_set(x_502, 2, x_492);
lean_ctor_set(x_502, 3, x_493);
lean_ctor_set_uint8(x_502, sizeof(void*)*4, x_500);
x_503 = 0;
x_504 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_504, 0, x_501);
lean_ctor_set(x_504, 1, x_496);
lean_ctor_set(x_504, 2, x_497);
lean_ctor_set(x_504, 3, x_502);
lean_ctor_set_uint8(x_504, sizeof(void*)*4, x_503);
return x_504;
}
else
{
lean_object* x_505; 
x_505 = lean_ctor_get(x_459, 3);
lean_inc(x_505);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; uint8_t x_509; lean_object* x_510; uint8_t x_511; lean_object* x_512; 
x_506 = lean_ctor_get(x_459, 1);
lean_inc(x_506);
x_507 = lean_ctor_get(x_459, 2);
lean_inc(x_507);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_508 = x_459;
} else {
 lean_dec_ref(x_459);
 x_508 = lean_box(0);
}
x_509 = 0;
if (lean_is_scalar(x_508)) {
 x_510 = lean_alloc_ctor(1, 4, 1);
} else {
 x_510 = x_508;
}
lean_ctor_set(x_510, 0, x_460);
lean_ctor_set(x_510, 1, x_506);
lean_ctor_set(x_510, 2, x_507);
lean_ctor_set(x_510, 3, x_505);
lean_ctor_set_uint8(x_510, sizeof(void*)*4, x_509);
x_511 = 1;
x_512 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_512, 0, x_362);
lean_ctor_set(x_512, 1, x_363);
lean_ctor_set(x_512, 2, x_364);
lean_ctor_set(x_512, 3, x_510);
lean_ctor_set_uint8(x_512, sizeof(void*)*4, x_511);
return x_512;
}
else
{
uint8_t x_513; 
x_513 = lean_ctor_get_uint8(x_505, sizeof(void*)*4);
if (x_513 == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; uint8_t x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; lean_object* x_527; 
x_514 = lean_ctor_get(x_459, 1);
lean_inc(x_514);
x_515 = lean_ctor_get(x_459, 2);
lean_inc(x_515);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_516 = x_459;
} else {
 lean_dec_ref(x_459);
 x_516 = lean_box(0);
}
x_517 = lean_ctor_get(x_505, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_505, 1);
lean_inc(x_518);
x_519 = lean_ctor_get(x_505, 2);
lean_inc(x_519);
x_520 = lean_ctor_get(x_505, 3);
lean_inc(x_520);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 lean_ctor_release(x_505, 2);
 lean_ctor_release(x_505, 3);
 x_521 = x_505;
} else {
 lean_dec_ref(x_505);
 x_521 = lean_box(0);
}
x_522 = 1;
lean_inc(x_460);
if (lean_is_scalar(x_521)) {
 x_523 = lean_alloc_ctor(1, 4, 1);
} else {
 x_523 = x_521;
}
lean_ctor_set(x_523, 0, x_362);
lean_ctor_set(x_523, 1, x_363);
lean_ctor_set(x_523, 2, x_364);
lean_ctor_set(x_523, 3, x_460);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 lean_ctor_release(x_460, 3);
 x_524 = x_460;
} else {
 lean_dec_ref(x_460);
 x_524 = lean_box(0);
}
lean_ctor_set_uint8(x_523, sizeof(void*)*4, x_522);
if (lean_is_scalar(x_524)) {
 x_525 = lean_alloc_ctor(1, 4, 1);
} else {
 x_525 = x_524;
}
lean_ctor_set(x_525, 0, x_517);
lean_ctor_set(x_525, 1, x_518);
lean_ctor_set(x_525, 2, x_519);
lean_ctor_set(x_525, 3, x_520);
lean_ctor_set_uint8(x_525, sizeof(void*)*4, x_522);
x_526 = 0;
if (lean_is_scalar(x_516)) {
 x_527 = lean_alloc_ctor(1, 4, 1);
} else {
 x_527 = x_516;
}
lean_ctor_set(x_527, 0, x_523);
lean_ctor_set(x_527, 1, x_514);
lean_ctor_set(x_527, 2, x_515);
lean_ctor_set(x_527, 3, x_525);
lean_ctor_set_uint8(x_527, sizeof(void*)*4, x_526);
return x_527;
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; uint8_t x_537; lean_object* x_538; uint8_t x_539; lean_object* x_540; 
x_528 = lean_ctor_get(x_459, 1);
lean_inc(x_528);
x_529 = lean_ctor_get(x_459, 2);
lean_inc(x_529);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_530 = x_459;
} else {
 lean_dec_ref(x_459);
 x_530 = lean_box(0);
}
x_531 = lean_ctor_get(x_460, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_460, 1);
lean_inc(x_532);
x_533 = lean_ctor_get(x_460, 2);
lean_inc(x_533);
x_534 = lean_ctor_get(x_460, 3);
lean_inc(x_534);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 lean_ctor_release(x_460, 3);
 x_535 = x_460;
} else {
 lean_dec_ref(x_460);
 x_535 = lean_box(0);
}
if (lean_is_scalar(x_535)) {
 x_536 = lean_alloc_ctor(1, 4, 1);
} else {
 x_536 = x_535;
}
lean_ctor_set(x_536, 0, x_531);
lean_ctor_set(x_536, 1, x_532);
lean_ctor_set(x_536, 2, x_533);
lean_ctor_set(x_536, 3, x_534);
lean_ctor_set_uint8(x_536, sizeof(void*)*4, x_513);
x_537 = 0;
if (lean_is_scalar(x_530)) {
 x_538 = lean_alloc_ctor(1, 4, 1);
} else {
 x_538 = x_530;
}
lean_ctor_set(x_538, 0, x_536);
lean_ctor_set(x_538, 1, x_528);
lean_ctor_set(x_538, 2, x_529);
lean_ctor_set(x_538, 3, x_505);
lean_ctor_set_uint8(x_538, sizeof(void*)*4, x_537);
x_539 = 1;
x_540 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_540, 0, x_362);
lean_ctor_set(x_540, 1, x_363);
lean_ctor_set(x_540, 2, x_364);
lean_ctor_set(x_540, 3, x_538);
lean_ctor_set_uint8(x_540, sizeof(void*)*4, x_539);
return x_540;
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_insert___at_Lean_Server_FileWorker_queueRequest___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Std_RBNode_ins___at_Lean_Server_FileWorker_queueRequest___spec__2(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_RBNode_ins___at_Lean_Server_FileWorker_queueRequest___spec__2(x_1, x_2, x_3);
x_7 = l_Std_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_queueRequest___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_RBNode_insert___at_Lean_Server_FileWorker_queueRequest___spec__1(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_queueRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_queueRequest___lambda__1), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
x_7 = l_Lean_Server_FileWorker_updatePendingRequests(x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_queueRequest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_queueRequest(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_FileWorker_handleRequest___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
x_6 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_IO_FS_Stream_writeLspMessage(x_1, x_6, x_3);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleRequest___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcConnectParams____x40_Lean_Data_Lsp_Extra___hyg_1068_(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Json_compress(x_1);
x_8 = l_Lean_Server_FileWorker_parseParams___rarg___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lean_Server_FileWorker_parseParams___rarg___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_6);
lean_dec(x_6);
x_13 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_IO_throwServerError___rarg(x_14, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_FileWorker_handleRequest___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_7 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonRpcConnected____x40_Lean_Data_Lsp_Extra___hyg_1178_(x_6);
x_8 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_IO_FS_Stream_writeLspMessage(x_1, x_8, x_3);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRequest___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_Server_RequestError_toLspResponseError(x_2, x_6);
lean_dec(x_6);
x_9 = l_IO_FS_Stream_writeLspResponseError(x_7, x_8, x_4);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_11);
lean_ctor_set(x_9, 0, x_3);
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_9);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_9, 0);
lean_ctor_set(x_3, 0, x_16);
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 0, x_3);
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
lean_ctor_set(x_3, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
lean_dec(x_3);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = l_Lean_Server_RequestError_toLspResponseError(x_2, x_20);
lean_dec(x_20);
x_23 = l_IO_FS_Stream_writeLspResponseError(x_21, x_22, x_4);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_24);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_31 = x_23;
} else {
 lean_dec_ref(x_23);
 x_31 = lean_box(0);
}
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
 lean_ctor_set_tag(x_33, 0);
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_3);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_3, 0);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
lean_dec(x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_IO_FS_Stream_writeLspResponse___at_Lean_Server_FileWorker_handleRequest___spec__1(x_36, x_37, x_4);
lean_dec(x_37);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_ctor_set(x_3, 0, x_40);
lean_ctor_set(x_38, 0, x_3);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_38, 0);
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_38);
lean_ctor_set(x_3, 0, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_3);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_38, 0);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_45);
lean_ctor_set_tag(x_38, 0);
lean_ctor_set(x_38, 0, x_3);
return x_38;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_38, 0);
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_38);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_3);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_3, 0);
lean_inc(x_49);
lean_dec(x_3);
x_50 = lean_ctor_get(x_1, 1);
lean_inc(x_50);
lean_dec(x_1);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_2);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_IO_FS_Stream_writeLspResponse___at_Lean_Server_FileWorker_handleRequest___spec__1(x_50, x_51, x_4);
lean_dec(x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_53);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_52, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_60 = x_52;
} else {
 lean_dec_ref(x_52);
 x_60 = lean_box(0);
}
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_58);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
 lean_ctor_set_tag(x_62, 0);
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRequest___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_3, 2);
x_31 = lean_ctor_get(x_1, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_3, 0);
x_33 = lean_ctor_get(x_1, 2);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_30);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_32);
lean_ctor_set(x_34, 3, x_33);
x_35 = l_Lean_Server_handleLspRequest(x_4, x_5, x_34, x_9);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_36);
x_10 = x_38;
x_11 = x_37;
goto block_29;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_39);
x_10 = x_41;
x_11 = x_40;
goto block_29;
}
block_29:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
lean_inc(x_2);
x_14 = l_Lean_Server_RequestError_toLspResponseError(x_2, x_12);
lean_dec(x_12);
x_15 = lean_alloc_closure((void*)(l_IO_FS_Stream_writeLspResponseError___boxed), 3, 2);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
x_16 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = l_Task_Priority_default;
x_18 = lean_io_as_task(x_16, x_17, x_11);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Server_FileWorker_queueRequest(x_2, x_19, x_7, x_8, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
lean_dec(x_10);
lean_inc(x_2);
x_23 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleRequest___lambda__1), 4, 2);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_2);
x_24 = l_Task_Priority_default;
x_25 = lean_io_map_task(x_23, x_22, x_24, x_11);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Server_FileWorker_queueRequest(x_2, x_26, x_7, x_8, x_27);
return x_28;
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleRequest___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("$/lean/rpc/connect");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Server_FileWorker_handleRequest___closed__1;
x_11 = lean_string_dec_eq(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
lean_inc(x_4);
x_13 = l_Lean_Server_FileWorker_handleRequest___lambda__2(x_4, x_1, x_8, x_2, x_3, x_12, x_4, x_5, x_9);
lean_dec(x_5);
lean_dec(x_8);
lean_dec(x_4);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_2);
x_14 = l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleRequest___spec__2(x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Server_FileWorker_handleRpcConnect___rarg(x_5, x_15);
lean_dec(x_5);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_dec(x_4);
lean_inc(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_17);
lean_inc(x_19);
x_21 = l_IO_FS_Stream_writeLspResponse___at_Lean_Server_FileWorker_handleRequest___spec__3(x_19, x_20, x_18);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_19);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_io_error_to_string(x_28);
x_31 = lean_box(0);
x_32 = 4;
x_33 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set(x_33, 2, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*3, x_32);
x_34 = l_IO_FS_Stream_writeLspResponseError(x_19, x_33, x_29);
lean_dec(x_33);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_34);
if (x_41 == 0)
{
return x_34;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_34, 0);
x_43 = lean_ctor_get(x_34, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_34);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_16, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_16, 1);
lean_inc(x_46);
lean_dec(x_16);
x_47 = lean_ctor_get(x_4, 1);
lean_inc(x_47);
lean_dec(x_4);
x_48 = lean_io_error_to_string(x_45);
x_49 = lean_box(0);
x_50 = 4;
x_51 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_48);
lean_ctor_set(x_51, 2, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*3, x_50);
x_52 = l_IO_FS_Stream_writeLspResponseError(x_47, x_51, x_46);
lean_dec(x_51);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
x_55 = lean_box(0);
lean_ctor_set(x_52, 0, x_55);
return x_52;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_dec(x_52);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_52);
if (x_59 == 0)
{
return x_52;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_52, 0);
x_61 = lean_ctor_get(x_52, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_52);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_5);
x_63 = lean_ctor_get(x_14, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_14, 1);
lean_inc(x_64);
lean_dec(x_14);
x_65 = lean_ctor_get(x_4, 1);
lean_inc(x_65);
lean_dec(x_4);
x_66 = lean_io_error_to_string(x_63);
x_67 = lean_box(0);
x_68 = 4;
x_69 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_66);
lean_ctor_set(x_69, 2, x_67);
lean_ctor_set_uint8(x_69, sizeof(void*)*3, x_68);
x_70 = l_IO_FS_Stream_writeLspResponseError(x_65, x_69, x_64);
lean_dec(x_69);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_70, 0);
lean_dec(x_72);
x_73 = lean_box(0);
lean_ctor_set(x_70, 0, x_73);
return x_70;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_70, 1);
lean_inc(x_74);
lean_dec(x_70);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_70);
if (x_77 == 0)
{
return x_70;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_70, 0);
x_79 = lean_ctor_get(x_70, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_70);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_FileWorker_handleRequest___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_writeLspResponse___at_Lean_Server_FileWorker_handleRequest___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleRequest___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleRequest___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRequest___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Server_FileWorker_handleRequest___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Std_RBNode_erase___at_Lean_Server_FileWorker_handleCancelRequest___spec__1(x_1, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
static lean_object* _init_l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Failed responding to request ");
return x_1;
}
}
static lean_object* _init_l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\"s\"");
return x_1;
}
}
static lean_object* _init_l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__1;
x_2 = l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(": ");
return x_1;
}
}
static lean_object* _init_l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__3;
x_2 = l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("null");
return x_1;
}
}
static lean_object* _init_l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__1;
x_2 = l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__7;
x_2 = l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1(x_1, x_7, x_3, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_io_has_finished(x_9, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_9);
lean_dec(x_8);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_1 = x_12;
x_2 = x_10;
x_5 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_task_get_own(x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_12);
lean_dec(x_10);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_io_error_to_string(x_21);
switch (lean_obj_tag(x_8)) {
case 0:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_8);
x_23 = l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__5;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = l_IO_throwServerError___rarg(x_26, x_19);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
case 1:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_32 = lean_ctor_get(x_8, 0);
lean_inc(x_32);
lean_dec(x_8);
x_33 = l_Lean_JsonNumber_toString(x_32);
x_34 = l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__1;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__4;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_string_append(x_37, x_22);
lean_dec(x_22);
x_39 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_40 = lean_string_append(x_38, x_39);
x_41 = l_IO_throwServerError___rarg(x_40, x_19);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_41);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_46 = l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__8;
x_47 = lean_string_append(x_46, x_22);
lean_dec(x_22);
x_48 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_49 = lean_string_append(x_47, x_48);
x_50 = l_IO_throwServerError___rarg(x_49, x_19);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
return x_50;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_50);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_20);
x_55 = lean_box(0);
x_56 = l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___lambda__1(x_8, x_12, x_55, x_19);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_1 = x_57;
x_2 = x_10;
x_5 = x_58;
goto _start;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_60 = !lean_is_exclusive(x_11);
if (x_60 == 0)
{
return x_11;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_11, 0);
x_62 = lean_ctor_get(x_11, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_11);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_del___at_Lean_Server_FileWorker_mainLoop___spec__3(uint64_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_unbox_uint64(x_6);
x_10 = lean_uint64_dec_lt(x_1, x_9);
if (x_10 == 0)
{
uint64_t x_11; uint8_t x_12; 
x_11 = lean_unbox_uint64(x_6);
x_12 = lean_uint64_dec_eq(x_1, x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Std_RBNode_isBlack___rarg(x_8);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Std_RBNode_del___at_Lean_Server_FileWorker_mainLoop___spec__3(x_1, x_8);
x_15 = 0;
lean_ctor_set(x_2, 3, x_14);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_15);
return x_2;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_free_object(x_2);
x_16 = l_Std_RBNode_del___at_Lean_Server_FileWorker_mainLoop___spec__3(x_1, x_8);
x_17 = l_Std_RBNode_balRight___rarg(x_5, x_6, x_7, x_16);
return x_17;
}
}
else
{
lean_object* x_18; 
lean_free_object(x_2);
lean_dec(x_7);
lean_dec(x_6);
x_18 = l_Std_RBNode_appendTrees___rarg(x_5, x_8);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = l_Std_RBNode_isBlack___rarg(x_5);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Std_RBNode_del___at_Lean_Server_FileWorker_mainLoop___spec__3(x_1, x_5);
x_21 = 0;
lean_ctor_set(x_2, 0, x_20);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_21);
return x_2;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_free_object(x_2);
x_22 = l_Std_RBNode_del___at_Lean_Server_FileWorker_mainLoop___spec__3(x_1, x_5);
x_23 = l_Std_RBNode_balLeft___rarg(x_22, x_6, x_7, x_8);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
x_26 = lean_ctor_get(x_2, 2);
x_27 = lean_ctor_get(x_2, 3);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_2);
x_28 = lean_unbox_uint64(x_25);
x_29 = lean_uint64_dec_lt(x_1, x_28);
if (x_29 == 0)
{
uint64_t x_30; uint8_t x_31; 
x_30 = lean_unbox_uint64(x_25);
x_31 = lean_uint64_dec_eq(x_1, x_30);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = l_Std_RBNode_isBlack___rarg(x_27);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_33 = l_Std_RBNode_del___at_Lean_Server_FileWorker_mainLoop___spec__3(x_1, x_27);
x_34 = 0;
x_35 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_35, 0, x_24);
lean_ctor_set(x_35, 1, x_25);
lean_ctor_set(x_35, 2, x_26);
lean_ctor_set(x_35, 3, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*4, x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_Std_RBNode_del___at_Lean_Server_FileWorker_mainLoop___spec__3(x_1, x_27);
x_37 = l_Std_RBNode_balRight___rarg(x_24, x_25, x_26, x_36);
return x_37;
}
}
else
{
lean_object* x_38; 
lean_dec(x_26);
lean_dec(x_25);
x_38 = l_Std_RBNode_appendTrees___rarg(x_24, x_27);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = l_Std_RBNode_isBlack___rarg(x_24);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_40 = l_Std_RBNode_del___at_Lean_Server_FileWorker_mainLoop___spec__3(x_1, x_24);
x_41 = 0;
x_42 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_25);
lean_ctor_set(x_42, 2, x_26);
lean_ctor_set(x_42, 3, x_27);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = l_Std_RBNode_del___at_Lean_Server_FileWorker_mainLoop___spec__3(x_1, x_24);
x_44 = l_Std_RBNode_balLeft___rarg(x_43, x_25, x_26, x_27);
return x_44;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_erase___at_Lean_Server_FileWorker_mainLoop___spec__2(uint64_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Std_RBNode_del___at_Lean_Server_FileWorker_mainLoop___spec__3(x_1, x_2);
x_4 = l_Std_RBNode_setBlack___rarg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_FileWorker_mainLoop___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 3);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l_Std_RBNode_forIn_visit___at_Lean_Server_FileWorker_mainLoop___spec__4(x_1, x_9, x_3, x_4, x_5, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_11, x_15);
lean_dec(x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Server_FileWorker_RpcSession_hasExpired(x_18, x_19);
lean_dec(x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_10);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_2 = x_12;
x_3 = x_16;
x_6 = x_23;
goto _start;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
lean_object* x_27; uint64_t x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_16, 2);
x_28 = lean_unbox_uint64(x_10);
lean_dec(x_10);
x_29 = l_Std_RBNode_erase___at_Lean_Server_FileWorker_mainLoop___spec__2(x_28, x_27);
lean_ctor_set(x_16, 2, x_29);
x_2 = x_12;
x_3 = x_16;
x_6 = x_25;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint64_t x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
x_33 = lean_ctor_get(x_16, 2);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_34 = lean_unbox_uint64(x_10);
lean_dec(x_10);
x_35 = l_Std_RBNode_erase___at_Lean_Server_FileWorker_mainLoop___spec__2(x_34, x_33);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_36, 2, x_35);
x_2 = x_12;
x_3 = x_36;
x_6 = x_25;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_FileWorker_mainLoop___spec__4___at_Lean_Server_FileWorker_mainLoop___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Std_RBNode_forIn_visit___at_Lean_Server_FileWorker_mainLoop___spec__4___at_Lean_Server_FileWorker_mainLoop___spec__5(x_8, x_2, x_3, x_4, x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_10, x_14);
lean_dec(x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Server_FileWorker_RpcSession_hasExpired(x_17, x_18);
lean_dec(x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_9);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_1 = x_11;
x_2 = x_15;
x_5 = x_22;
goto _start;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
lean_object* x_26; uint64_t x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 2);
x_27 = lean_unbox_uint64(x_9);
lean_dec(x_9);
x_28 = l_Std_RBNode_erase___at_Lean_Server_FileWorker_mainLoop___spec__2(x_27, x_26);
lean_ctor_set(x_15, 2, x_28);
x_1 = x_11;
x_2 = x_15;
x_5 = x_24;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint64_t x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_15, 1);
x_32 = lean_ctor_get(x_15, 2);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_15);
x_33 = lean_unbox_uint64(x_9);
lean_dec(x_9);
x_34 = l_Std_RBNode_erase___at_Lean_Server_FileWorker_mainLoop___spec__2(x_33, x_32);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set(x_35, 2, x_34);
x_1 = x_11;
x_2 = x_35;
x_5 = x_24;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_mainLoop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Got invalid JSON-RPC message");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_mainLoop___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("exit");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_mainLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = l_IO_FS_Stream_readLspMessage(x_7, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_97; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_97 = !lean_is_exclusive(x_5);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_5, 0);
x_99 = lean_ctor_get(x_5, 1);
x_100 = lean_ctor_get(x_5, 2);
lean_inc(x_99);
x_101 = l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1(x_99, x_99, x_1, x_2, x_10);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
lean_inc(x_100);
lean_ctor_set(x_5, 1, x_102);
x_104 = l_Std_RBNode_forIn_visit___at_Lean_Server_FileWorker_mainLoop___spec__4___at_Lean_Server_FileWorker_mainLoop___spec__5(x_100, x_5, x_1, x_2, x_103);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_st_ref_set(x_2, x_107, x_106);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_11 = x_109;
goto block_96;
}
else
{
uint8_t x_110; 
lean_free_object(x_5);
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_101);
if (x_110 == 0)
{
return x_101;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_101, 0);
x_112 = lean_ctor_get(x_101, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_101);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_5, 0);
x_115 = lean_ctor_get(x_5, 1);
x_116 = lean_ctor_get(x_5, 2);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_5);
lean_inc(x_115);
x_117 = l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1(x_115, x_115, x_1, x_2, x_10);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
lean_inc(x_116);
x_120 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_120, 0, x_114);
lean_ctor_set(x_120, 1, x_118);
lean_ctor_set(x_120, 2, x_116);
x_121 = l_Std_RBNode_forIn_visit___at_Lean_Server_FileWorker_mainLoop___spec__4___at_Lean_Server_FileWorker_mainLoop___spec__5(x_116, x_120, x_1, x_2, x_119);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_st_ref_set(x_2, x_124, x_123);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
x_11 = x_126;
goto block_96;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_116);
lean_dec(x_114);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_127 = lean_ctor_get(x_117, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_117, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_129 = x_117;
} else {
 lean_dec_ref(x_117);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
}
block_96:
{
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 2);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Server_FileWorker_mainLoop___closed__1;
x_14 = l_IO_throwServerError___rarg(x_13, x_11);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_2);
lean_inc(x_1);
x_20 = l_Lean_Server_FileWorker_handleRequest(x_16, x_17, x_19, x_1, x_2, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_3 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_9, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_dec(x_9);
x_29 = lean_ctor_get(x_15, 0);
lean_inc(x_29);
lean_dec(x_15);
x_30 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_inc(x_2);
lean_inc(x_1);
x_31 = l_Lean_Server_FileWorker_handleRequest(x_27, x_28, x_30, x_1, x_2, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_3 = x_32;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_31);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
case 1:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_9, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_9, 1);
lean_inc(x_39);
lean_dec(x_9);
x_40 = l_Lean_Server_FileWorker_mainLoop___closed__2;
x_41 = lean_string_dec_eq(x_38, x_40);
if (x_41 == 0)
{
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_38);
lean_dec(x_2);
lean_dec(x_1);
x_42 = l_Lean_Server_FileWorker_mainLoop___closed__1;
x_43 = l_IO_throwServerError___rarg(x_42, x_11);
return x_43;
}
else
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_39, 0);
lean_inc(x_44);
lean_dec(x_39);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_inc(x_2);
lean_inc(x_1);
x_47 = l_Lean_Server_FileWorker_handleNotification(x_38, x_46, x_1, x_2, x_11);
lean_dec(x_38);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_3 = x_48;
goto _start;
}
else
{
uint8_t x_50; 
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_47);
if (x_50 == 0)
{
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 0);
x_52 = lean_ctor_get(x_47, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_47);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_44, 0);
lean_inc(x_54);
lean_dec(x_44);
x_55 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_inc(x_2);
lean_inc(x_1);
x_56 = l_Lean_Server_FileWorker_handleNotification(x_38, x_55, x_1, x_2, x_11);
lean_dec(x_38);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_3 = x_57;
goto _start;
}
else
{
uint8_t x_59; 
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_56);
if (x_59 == 0)
{
return x_56;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_56, 0);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_56);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
}
else
{
lean_dec(x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
lean_dec(x_1);
x_63 = lean_st_ref_get(x_2, x_11);
lean_dec(x_2);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_66, 3);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l_Lean_Server_FileWorker_CancelToken_set(x_67, x_65);
lean_dec(x_67);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_68, 0);
lean_dec(x_70);
x_71 = lean_box(0);
lean_ctor_set(x_68, 0, x_71);
return x_68;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_68, 1);
lean_inc(x_72);
lean_dec(x_68);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_39, 0);
lean_inc(x_75);
lean_dec(x_39);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_77, 0, x_76);
lean_inc(x_2);
lean_inc(x_1);
x_78 = l_Lean_Server_FileWorker_handleNotification(x_40, x_77, x_1, x_2, x_11);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_3 = x_79;
goto _start;
}
else
{
uint8_t x_81; 
lean_dec(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_78);
if (x_81 == 0)
{
return x_78;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_78, 0);
x_83 = lean_ctor_get(x_78, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_78);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_75, 0);
lean_inc(x_85);
lean_dec(x_75);
x_86 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_86, 0, x_85);
lean_inc(x_2);
lean_inc(x_1);
x_87 = l_Lean_Server_FileWorker_handleNotification(x_40, x_86, x_1, x_2, x_11);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_3 = x_88;
goto _start;
}
else
{
uint8_t x_90; 
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_87);
if (x_90 == 0)
{
return x_87;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_87, 0);
x_92 = lean_ctor_get(x_87, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_87);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
}
}
default: 
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_94 = l_Lean_Server_FileWorker_mainLoop___closed__1;
x_95 = l_IO_throwServerError___rarg(x_94, x_11);
return x_95;
}
}
}
}
else
{
uint8_t x_131; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_131 = !lean_is_exclusive(x_8);
if (x_131 == 0)
{
return x_8;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_8, 0);
x_133 = lean_ctor_get(x_8, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_8);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_del___at_Lean_Server_FileWorker_mainLoop___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Std_RBNode_del___at_Lean_Server_FileWorker_mainLoop___spec__3(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_erase___at_Lean_Server_FileWorker_mainLoop___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Std_RBNode_erase___at_Lean_Server_FileWorker_mainLoop___spec__2(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_FileWorker_mainLoop___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_RBNode_forIn_visit___at_Lean_Server_FileWorker_mainLoop___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_FileWorker_mainLoop___spec__4___at_Lean_Server_FileWorker_mainLoop___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_RBNode_forIn_visit___at_Lean_Server_FileWorker_mainLoop___spec__4___at_Lean_Server_FileWorker_mainLoop___spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Expected method '");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', got method '");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("processId");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("clientInfo");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("rootUri");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("initializationOptions");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("trace");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("workspaceFolders");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("2.0");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("jsonrpc");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__12;
x_2 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__11;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("method");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("params");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Expected JSON-RPC request, got: '");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("result");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("id");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__18;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("message");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("data");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("code");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("error");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32700u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__24;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__25;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__26;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32600u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__28;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__29;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__30;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32601u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__32;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__33;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__34;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32602u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__36;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__37;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__38;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32603u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__40;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__41;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__42;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32002u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__44;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__45;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__46;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32001u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__48;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__49;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__50;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32801u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__52;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__54() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__53;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__54;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__56() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32800u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__57() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__56;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__57;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__59() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__58;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__60() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32900u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__61() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__60;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__62() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__61;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__63() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__62;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_readMessage(x_1, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 2);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_string_dec_eq(x_10, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_9);
x_13 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__1;
x_14 = lean_string_append(x_13, x_3);
lean_dec(x_3);
x_15 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_string_append(x_16, x_10);
lean_dec(x_10);
x_18 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_20, 0, x_19);
if (lean_is_scalar(x_8)) {
 x_21 = lean_alloc_ctor(1, 2, 0);
} else {
 x_21 = x_8;
 lean_ctor_set_tag(x_21, 1);
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_7);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_236; 
x_236 = lean_box(0);
x_22 = x_236;
goto block_235;
}
else
{
lean_object* x_237; 
x_237 = lean_ctor_get(x_11, 0);
lean_inc(x_237);
lean_dec(x_11);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
lean_dec(x_237);
x_239 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_239, 0, x_238);
x_22 = x_239;
goto block_235;
}
else
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_ctor_get(x_237, 0);
lean_inc(x_240);
lean_dec(x_237);
x_241 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_241, 0, x_240);
x_22 = x_241;
goto block_235;
}
}
block_235:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_23 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__4;
x_24 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__1(x_22, x_23);
x_25 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__5;
x_26 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__2(x_22, x_25);
x_27 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__6;
x_28 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_22, x_27);
x_29 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__7;
x_30 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__3(x_22, x_29);
x_31 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__8;
x_32 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__5(x_22, x_31);
x_33 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__9;
x_34 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__6(x_22, x_33);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_232; 
lean_dec(x_32);
x_232 = 0;
x_35 = x_232;
goto block_231;
}
else
{
lean_object* x_233; uint8_t x_234; 
x_233 = lean_ctor_get(x_32, 0);
lean_inc(x_233);
lean_dec(x_32);
x_234 = lean_unbox(x_233);
lean_dec(x_233);
x_35 = x_234;
goto block_231;
}
block_231:
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_36; 
lean_dec(x_24);
x_36 = lean_box(0);
if (lean_obj_tag(x_26) == 0)
{
lean_dec(x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_dec(x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_30);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_34);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_38, 2, x_36);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 4, x_37);
lean_ctor_set(x_38, 5, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*6, x_35);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_9);
lean_ctor_set(x_39, 1, x_3);
lean_ctor_set(x_39, 2, x_38);
if (lean_is_scalar(x_8)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_8;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_7);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_34, 0);
lean_inc(x_41);
lean_dec(x_34);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_44, 0, x_36);
lean_ctor_set(x_44, 1, x_36);
lean_ctor_set(x_44, 2, x_36);
lean_ctor_set(x_44, 3, x_36);
lean_ctor_set(x_44, 4, x_43);
lean_ctor_set(x_44, 5, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*6, x_35);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_9);
lean_ctor_set(x_45, 1, x_3);
lean_ctor_set(x_45, 2, x_44);
if (lean_is_scalar(x_8)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_8;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_7);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_30, 0);
lean_inc(x_47);
lean_dec(x_30);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_34);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_50, 0, x_36);
lean_ctor_set(x_50, 1, x_36);
lean_ctor_set(x_50, 2, x_36);
lean_ctor_set(x_50, 3, x_48);
lean_ctor_set(x_50, 4, x_49);
lean_ctor_set(x_50, 5, x_36);
lean_ctor_set_uint8(x_50, sizeof(void*)*6, x_35);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_9);
lean_ctor_set(x_51, 1, x_3);
lean_ctor_set(x_51, 2, x_50);
if (lean_is_scalar(x_8)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_8;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_7);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_34, 0);
lean_inc(x_53);
lean_dec(x_34);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_56, 0, x_36);
lean_ctor_set(x_56, 1, x_36);
lean_ctor_set(x_56, 2, x_36);
lean_ctor_set(x_56, 3, x_48);
lean_ctor_set(x_56, 4, x_55);
lean_ctor_set(x_56, 5, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*6, x_35);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_9);
lean_ctor_set(x_57, 1, x_3);
lean_ctor_set(x_57, 2, x_56);
if (lean_is_scalar(x_8)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_8;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_7);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_28, 0);
lean_inc(x_59);
lean_dec(x_28);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_30);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_34);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_62, 0, x_36);
lean_ctor_set(x_62, 1, x_36);
lean_ctor_set(x_62, 2, x_60);
lean_ctor_set(x_62, 3, x_36);
lean_ctor_set(x_62, 4, x_61);
lean_ctor_set(x_62, 5, x_36);
lean_ctor_set_uint8(x_62, sizeof(void*)*6, x_35);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_9);
lean_ctor_set(x_63, 1, x_3);
lean_ctor_set(x_63, 2, x_62);
if (lean_is_scalar(x_8)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_8;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_7);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_34, 0);
lean_inc(x_65);
lean_dec(x_34);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_68, 0, x_36);
lean_ctor_set(x_68, 1, x_36);
lean_ctor_set(x_68, 2, x_60);
lean_ctor_set(x_68, 3, x_36);
lean_ctor_set(x_68, 4, x_67);
lean_ctor_set(x_68, 5, x_66);
lean_ctor_set_uint8(x_68, sizeof(void*)*6, x_35);
x_69 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_69, 0, x_9);
lean_ctor_set(x_69, 1, x_3);
lean_ctor_set(x_69, 2, x_68);
if (lean_is_scalar(x_8)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_8;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_7);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_30, 0);
lean_inc(x_71);
lean_dec(x_30);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_34);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_74, 0, x_36);
lean_ctor_set(x_74, 1, x_36);
lean_ctor_set(x_74, 2, x_60);
lean_ctor_set(x_74, 3, x_72);
lean_ctor_set(x_74, 4, x_73);
lean_ctor_set(x_74, 5, x_36);
lean_ctor_set_uint8(x_74, sizeof(void*)*6, x_35);
x_75 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_75, 0, x_9);
lean_ctor_set(x_75, 1, x_3);
lean_ctor_set(x_75, 2, x_74);
if (lean_is_scalar(x_8)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_8;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_7);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_34, 0);
lean_inc(x_77);
lean_dec(x_34);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_80, 0, x_36);
lean_ctor_set(x_80, 1, x_36);
lean_ctor_set(x_80, 2, x_60);
lean_ctor_set(x_80, 3, x_72);
lean_ctor_set(x_80, 4, x_79);
lean_ctor_set(x_80, 5, x_78);
lean_ctor_set_uint8(x_80, sizeof(void*)*6, x_35);
x_81 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_81, 0, x_9);
lean_ctor_set(x_81, 1, x_3);
lean_ctor_set(x_81, 2, x_80);
if (lean_is_scalar(x_8)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_8;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_7);
return x_82;
}
}
}
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_26, 0);
lean_inc(x_83);
lean_dec(x_26);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
if (lean_obj_tag(x_28) == 0)
{
lean_dec(x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_30);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_34);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_86, 0, x_36);
lean_ctor_set(x_86, 1, x_84);
lean_ctor_set(x_86, 2, x_36);
lean_ctor_set(x_86, 3, x_36);
lean_ctor_set(x_86, 4, x_85);
lean_ctor_set(x_86, 5, x_36);
lean_ctor_set_uint8(x_86, sizeof(void*)*6, x_35);
x_87 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_87, 0, x_9);
lean_ctor_set(x_87, 1, x_3);
lean_ctor_set(x_87, 2, x_86);
if (lean_is_scalar(x_8)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_8;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_7);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = lean_ctor_get(x_34, 0);
lean_inc(x_89);
lean_dec(x_34);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_92, 0, x_36);
lean_ctor_set(x_92, 1, x_84);
lean_ctor_set(x_92, 2, x_36);
lean_ctor_set(x_92, 3, x_36);
lean_ctor_set(x_92, 4, x_91);
lean_ctor_set(x_92, 5, x_90);
lean_ctor_set_uint8(x_92, sizeof(void*)*6, x_35);
x_93 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_93, 0, x_9);
lean_ctor_set(x_93, 1, x_3);
lean_ctor_set(x_93, 2, x_92);
if (lean_is_scalar(x_8)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_8;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_7);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_30, 0);
lean_inc(x_95);
lean_dec(x_30);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_34);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_98, 0, x_36);
lean_ctor_set(x_98, 1, x_84);
lean_ctor_set(x_98, 2, x_36);
lean_ctor_set(x_98, 3, x_96);
lean_ctor_set(x_98, 4, x_97);
lean_ctor_set(x_98, 5, x_36);
lean_ctor_set_uint8(x_98, sizeof(void*)*6, x_35);
x_99 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_99, 0, x_9);
lean_ctor_set(x_99, 1, x_3);
lean_ctor_set(x_99, 2, x_98);
if (lean_is_scalar(x_8)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_8;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_7);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_101 = lean_ctor_get(x_34, 0);
lean_inc(x_101);
lean_dec(x_34);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = lean_box(0);
x_104 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_104, 0, x_36);
lean_ctor_set(x_104, 1, x_84);
lean_ctor_set(x_104, 2, x_36);
lean_ctor_set(x_104, 3, x_96);
lean_ctor_set(x_104, 4, x_103);
lean_ctor_set(x_104, 5, x_102);
lean_ctor_set_uint8(x_104, sizeof(void*)*6, x_35);
x_105 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_105, 0, x_9);
lean_ctor_set(x_105, 1, x_3);
lean_ctor_set(x_105, 2, x_104);
if (lean_is_scalar(x_8)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_8;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_7);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_28, 0);
lean_inc(x_107);
lean_dec(x_28);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_30);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_34);
x_109 = lean_box(0);
x_110 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_110, 0, x_36);
lean_ctor_set(x_110, 1, x_84);
lean_ctor_set(x_110, 2, x_108);
lean_ctor_set(x_110, 3, x_36);
lean_ctor_set(x_110, 4, x_109);
lean_ctor_set(x_110, 5, x_36);
lean_ctor_set_uint8(x_110, sizeof(void*)*6, x_35);
x_111 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_111, 0, x_9);
lean_ctor_set(x_111, 1, x_3);
lean_ctor_set(x_111, 2, x_110);
if (lean_is_scalar(x_8)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_8;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_7);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_113 = lean_ctor_get(x_34, 0);
lean_inc(x_113);
lean_dec(x_34);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = lean_box(0);
x_116 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_116, 0, x_36);
lean_ctor_set(x_116, 1, x_84);
lean_ctor_set(x_116, 2, x_108);
lean_ctor_set(x_116, 3, x_36);
lean_ctor_set(x_116, 4, x_115);
lean_ctor_set(x_116, 5, x_114);
lean_ctor_set_uint8(x_116, sizeof(void*)*6, x_35);
x_117 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_117, 0, x_9);
lean_ctor_set(x_117, 1, x_3);
lean_ctor_set(x_117, 2, x_116);
if (lean_is_scalar(x_8)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_8;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_7);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_30, 0);
lean_inc(x_119);
lean_dec(x_30);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_119);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_34);
x_121 = lean_box(0);
x_122 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_122, 0, x_36);
lean_ctor_set(x_122, 1, x_84);
lean_ctor_set(x_122, 2, x_108);
lean_ctor_set(x_122, 3, x_120);
lean_ctor_set(x_122, 4, x_121);
lean_ctor_set(x_122, 5, x_36);
lean_ctor_set_uint8(x_122, sizeof(void*)*6, x_35);
x_123 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_123, 0, x_9);
lean_ctor_set(x_123, 1, x_3);
lean_ctor_set(x_123, 2, x_122);
if (lean_is_scalar(x_8)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_8;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_7);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_125 = lean_ctor_get(x_34, 0);
lean_inc(x_125);
lean_dec(x_34);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_127 = lean_box(0);
x_128 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_128, 0, x_36);
lean_ctor_set(x_128, 1, x_84);
lean_ctor_set(x_128, 2, x_108);
lean_ctor_set(x_128, 3, x_120);
lean_ctor_set(x_128, 4, x_127);
lean_ctor_set(x_128, 5, x_126);
lean_ctor_set_uint8(x_128, sizeof(void*)*6, x_35);
x_129 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_129, 0, x_9);
lean_ctor_set(x_129, 1, x_3);
lean_ctor_set(x_129, 2, x_128);
if (lean_is_scalar(x_8)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_8;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_7);
return x_130;
}
}
}
}
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_24, 0);
lean_inc(x_131);
lean_dec(x_24);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_131);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_133; 
lean_dec(x_26);
x_133 = lean_box(0);
if (lean_obj_tag(x_28) == 0)
{
lean_dec(x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_30);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_34);
x_134 = lean_box(0);
x_135 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
lean_ctor_set(x_135, 2, x_133);
lean_ctor_set(x_135, 3, x_133);
lean_ctor_set(x_135, 4, x_134);
lean_ctor_set(x_135, 5, x_133);
lean_ctor_set_uint8(x_135, sizeof(void*)*6, x_35);
x_136 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_136, 0, x_9);
lean_ctor_set(x_136, 1, x_3);
lean_ctor_set(x_136, 2, x_135);
if (lean_is_scalar(x_8)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_8;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_7);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_138 = lean_ctor_get(x_34, 0);
lean_inc(x_138);
lean_dec(x_34);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
x_140 = lean_box(0);
x_141 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_141, 0, x_132);
lean_ctor_set(x_141, 1, x_133);
lean_ctor_set(x_141, 2, x_133);
lean_ctor_set(x_141, 3, x_133);
lean_ctor_set(x_141, 4, x_140);
lean_ctor_set(x_141, 5, x_139);
lean_ctor_set_uint8(x_141, sizeof(void*)*6, x_35);
x_142 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_142, 0, x_9);
lean_ctor_set(x_142, 1, x_3);
lean_ctor_set(x_142, 2, x_141);
if (lean_is_scalar(x_8)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_8;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_7);
return x_143;
}
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_30, 0);
lean_inc(x_144);
lean_dec(x_30);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_144);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_34);
x_146 = lean_box(0);
x_147 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_147, 0, x_132);
lean_ctor_set(x_147, 1, x_133);
lean_ctor_set(x_147, 2, x_133);
lean_ctor_set(x_147, 3, x_145);
lean_ctor_set(x_147, 4, x_146);
lean_ctor_set(x_147, 5, x_133);
lean_ctor_set_uint8(x_147, sizeof(void*)*6, x_35);
x_148 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_148, 0, x_9);
lean_ctor_set(x_148, 1, x_3);
lean_ctor_set(x_148, 2, x_147);
if (lean_is_scalar(x_8)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_8;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_7);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_150 = lean_ctor_get(x_34, 0);
lean_inc(x_150);
lean_dec(x_34);
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_150);
x_152 = lean_box(0);
x_153 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_153, 0, x_132);
lean_ctor_set(x_153, 1, x_133);
lean_ctor_set(x_153, 2, x_133);
lean_ctor_set(x_153, 3, x_145);
lean_ctor_set(x_153, 4, x_152);
lean_ctor_set(x_153, 5, x_151);
lean_ctor_set_uint8(x_153, sizeof(void*)*6, x_35);
x_154 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_154, 0, x_9);
lean_ctor_set(x_154, 1, x_3);
lean_ctor_set(x_154, 2, x_153);
if (lean_is_scalar(x_8)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_8;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_7);
return x_155;
}
}
}
else
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_28, 0);
lean_inc(x_156);
lean_dec(x_28);
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_156);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_30);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_34);
x_158 = lean_box(0);
x_159 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_159, 0, x_132);
lean_ctor_set(x_159, 1, x_133);
lean_ctor_set(x_159, 2, x_157);
lean_ctor_set(x_159, 3, x_133);
lean_ctor_set(x_159, 4, x_158);
lean_ctor_set(x_159, 5, x_133);
lean_ctor_set_uint8(x_159, sizeof(void*)*6, x_35);
x_160 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_160, 0, x_9);
lean_ctor_set(x_160, 1, x_3);
lean_ctor_set(x_160, 2, x_159);
if (lean_is_scalar(x_8)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_8;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_7);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_162 = lean_ctor_get(x_34, 0);
lean_inc(x_162);
lean_dec(x_34);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_162);
x_164 = lean_box(0);
x_165 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_165, 0, x_132);
lean_ctor_set(x_165, 1, x_133);
lean_ctor_set(x_165, 2, x_157);
lean_ctor_set(x_165, 3, x_133);
lean_ctor_set(x_165, 4, x_164);
lean_ctor_set(x_165, 5, x_163);
lean_ctor_set_uint8(x_165, sizeof(void*)*6, x_35);
x_166 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_166, 0, x_9);
lean_ctor_set(x_166, 1, x_3);
lean_ctor_set(x_166, 2, x_165);
if (lean_is_scalar(x_8)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_8;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_7);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_30, 0);
lean_inc(x_168);
lean_dec(x_30);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_168);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_34);
x_170 = lean_box(0);
x_171 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_171, 0, x_132);
lean_ctor_set(x_171, 1, x_133);
lean_ctor_set(x_171, 2, x_157);
lean_ctor_set(x_171, 3, x_169);
lean_ctor_set(x_171, 4, x_170);
lean_ctor_set(x_171, 5, x_133);
lean_ctor_set_uint8(x_171, sizeof(void*)*6, x_35);
x_172 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_172, 0, x_9);
lean_ctor_set(x_172, 1, x_3);
lean_ctor_set(x_172, 2, x_171);
if (lean_is_scalar(x_8)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_8;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_7);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_174 = lean_ctor_get(x_34, 0);
lean_inc(x_174);
lean_dec(x_34);
x_175 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_175, 0, x_174);
x_176 = lean_box(0);
x_177 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_177, 0, x_132);
lean_ctor_set(x_177, 1, x_133);
lean_ctor_set(x_177, 2, x_157);
lean_ctor_set(x_177, 3, x_169);
lean_ctor_set(x_177, 4, x_176);
lean_ctor_set(x_177, 5, x_175);
lean_ctor_set_uint8(x_177, sizeof(void*)*6, x_35);
x_178 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_178, 0, x_9);
lean_ctor_set(x_178, 1, x_3);
lean_ctor_set(x_178, 2, x_177);
if (lean_is_scalar(x_8)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_8;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_7);
return x_179;
}
}
}
}
else
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_26, 0);
lean_inc(x_180);
lean_dec(x_26);
x_181 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_181, 0, x_180);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_182; 
lean_dec(x_28);
x_182 = lean_box(0);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_30);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_34);
x_183 = lean_box(0);
x_184 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_184, 0, x_132);
lean_ctor_set(x_184, 1, x_181);
lean_ctor_set(x_184, 2, x_182);
lean_ctor_set(x_184, 3, x_182);
lean_ctor_set(x_184, 4, x_183);
lean_ctor_set(x_184, 5, x_182);
lean_ctor_set_uint8(x_184, sizeof(void*)*6, x_35);
x_185 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_185, 0, x_9);
lean_ctor_set(x_185, 1, x_3);
lean_ctor_set(x_185, 2, x_184);
if (lean_is_scalar(x_8)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_8;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_7);
return x_186;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_187 = lean_ctor_get(x_34, 0);
lean_inc(x_187);
lean_dec(x_34);
x_188 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_188, 0, x_187);
x_189 = lean_box(0);
x_190 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_190, 0, x_132);
lean_ctor_set(x_190, 1, x_181);
lean_ctor_set(x_190, 2, x_182);
lean_ctor_set(x_190, 3, x_182);
lean_ctor_set(x_190, 4, x_189);
lean_ctor_set(x_190, 5, x_188);
lean_ctor_set_uint8(x_190, sizeof(void*)*6, x_35);
x_191 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_191, 0, x_9);
lean_ctor_set(x_191, 1, x_3);
lean_ctor_set(x_191, 2, x_190);
if (lean_is_scalar(x_8)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_8;
}
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_7);
return x_192;
}
}
else
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_ctor_get(x_30, 0);
lean_inc(x_193);
lean_dec(x_30);
x_194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_194, 0, x_193);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_34);
x_195 = lean_box(0);
x_196 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_196, 0, x_132);
lean_ctor_set(x_196, 1, x_181);
lean_ctor_set(x_196, 2, x_182);
lean_ctor_set(x_196, 3, x_194);
lean_ctor_set(x_196, 4, x_195);
lean_ctor_set(x_196, 5, x_182);
lean_ctor_set_uint8(x_196, sizeof(void*)*6, x_35);
x_197 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_197, 0, x_9);
lean_ctor_set(x_197, 1, x_3);
lean_ctor_set(x_197, 2, x_196);
if (lean_is_scalar(x_8)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_8;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_7);
return x_198;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_199 = lean_ctor_get(x_34, 0);
lean_inc(x_199);
lean_dec(x_34);
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_199);
x_201 = lean_box(0);
x_202 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_202, 0, x_132);
lean_ctor_set(x_202, 1, x_181);
lean_ctor_set(x_202, 2, x_182);
lean_ctor_set(x_202, 3, x_194);
lean_ctor_set(x_202, 4, x_201);
lean_ctor_set(x_202, 5, x_200);
lean_ctor_set_uint8(x_202, sizeof(void*)*6, x_35);
x_203 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_203, 0, x_9);
lean_ctor_set(x_203, 1, x_3);
lean_ctor_set(x_203, 2, x_202);
if (lean_is_scalar(x_8)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_8;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_7);
return x_204;
}
}
}
else
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_28, 0);
lean_inc(x_205);
lean_dec(x_28);
x_206 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_206, 0, x_205);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_207; 
lean_dec(x_30);
x_207 = lean_box(0);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_34);
x_208 = lean_box(0);
x_209 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_209, 0, x_132);
lean_ctor_set(x_209, 1, x_181);
lean_ctor_set(x_209, 2, x_206);
lean_ctor_set(x_209, 3, x_207);
lean_ctor_set(x_209, 4, x_208);
lean_ctor_set(x_209, 5, x_207);
lean_ctor_set_uint8(x_209, sizeof(void*)*6, x_35);
x_210 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_210, 0, x_9);
lean_ctor_set(x_210, 1, x_3);
lean_ctor_set(x_210, 2, x_209);
if (lean_is_scalar(x_8)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_8;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_7);
return x_211;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_212 = lean_ctor_get(x_34, 0);
lean_inc(x_212);
lean_dec(x_34);
x_213 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_213, 0, x_212);
x_214 = lean_box(0);
x_215 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_215, 0, x_132);
lean_ctor_set(x_215, 1, x_181);
lean_ctor_set(x_215, 2, x_206);
lean_ctor_set(x_215, 3, x_207);
lean_ctor_set(x_215, 4, x_214);
lean_ctor_set(x_215, 5, x_213);
lean_ctor_set_uint8(x_215, sizeof(void*)*6, x_35);
x_216 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_216, 0, x_9);
lean_ctor_set(x_216, 1, x_3);
lean_ctor_set(x_216, 2, x_215);
if (lean_is_scalar(x_8)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_8;
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_7);
return x_217;
}
}
else
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_30, 0);
lean_inc(x_218);
lean_dec(x_30);
x_219 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_219, 0, x_218);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_34);
x_220 = lean_box(0);
x_221 = lean_box(0);
x_222 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_222, 0, x_132);
lean_ctor_set(x_222, 1, x_181);
lean_ctor_set(x_222, 2, x_206);
lean_ctor_set(x_222, 3, x_219);
lean_ctor_set(x_222, 4, x_221);
lean_ctor_set(x_222, 5, x_220);
lean_ctor_set_uint8(x_222, sizeof(void*)*6, x_35);
x_223 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_223, 0, x_9);
lean_ctor_set(x_223, 1, x_3);
lean_ctor_set(x_223, 2, x_222);
if (lean_is_scalar(x_8)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_8;
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_7);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_225 = lean_ctor_get(x_34, 0);
lean_inc(x_225);
lean_dec(x_34);
x_226 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_226, 0, x_225);
x_227 = lean_box(0);
x_228 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_228, 0, x_132);
lean_ctor_set(x_228, 1, x_181);
lean_ctor_set(x_228, 2, x_206);
lean_ctor_set(x_228, 3, x_219);
lean_ctor_set(x_228, 4, x_227);
lean_ctor_set(x_228, 5, x_226);
lean_ctor_set_uint8(x_228, sizeof(void*)*6, x_35);
x_229 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_229, 0, x_9);
lean_ctor_set(x_229, 1, x_3);
lean_ctor_set(x_229, 2, x_228);
if (lean_is_scalar(x_8)) {
 x_230 = lean_alloc_ctor(0, 2, 0);
} else {
 x_230 = x_8;
}
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_7);
return x_230;
}
}
}
}
}
}
}
}
}
case 1:
{
uint8_t x_242; 
lean_dec(x_3);
x_242 = !lean_is_exclusive(x_5);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_243 = lean_ctor_get(x_5, 0);
lean_dec(x_243);
x_244 = lean_ctor_get(x_6, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_6, 1);
lean_inc(x_245);
lean_dec(x_6);
x_246 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_246, 0, x_244);
x_247 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__14;
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_246);
x_249 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__15;
x_250 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_249, x_245);
lean_dec(x_245);
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_248);
lean_ctor_set(x_251, 1, x_250);
x_252 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13;
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_251);
x_254 = l_Lean_Json_mkObj(x_253);
x_255 = l_Lean_Json_compress(x_254);
x_256 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_257 = lean_string_append(x_256, x_255);
lean_dec(x_255);
x_258 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3;
x_259 = lean_string_append(x_257, x_258);
x_260 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_260);
return x_5;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_261 = lean_ctor_get(x_5, 1);
lean_inc(x_261);
lean_dec(x_5);
x_262 = lean_ctor_get(x_6, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_6, 1);
lean_inc(x_263);
lean_dec(x_6);
x_264 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_264, 0, x_262);
x_265 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__14;
x_266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_264);
x_267 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__15;
x_268 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_267, x_263);
lean_dec(x_263);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_266);
lean_ctor_set(x_269, 1, x_268);
x_270 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13;
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_269);
x_272 = l_Lean_Json_mkObj(x_271);
x_273 = l_Lean_Json_compress(x_272);
x_274 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_275 = lean_string_append(x_274, x_273);
lean_dec(x_273);
x_276 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3;
x_277 = lean_string_append(x_275, x_276);
x_278 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_278, 0, x_277);
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_261);
return x_279;
}
}
case 2:
{
uint8_t x_280; 
lean_dec(x_3);
x_280 = !lean_is_exclusive(x_5);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_281 = lean_ctor_get(x_5, 0);
lean_dec(x_281);
x_282 = lean_ctor_get(x_6, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_6, 1);
lean_inc(x_283);
lean_dec(x_6);
x_284 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__17;
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_283);
x_286 = lean_box(0);
x_287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
switch (lean_obj_tag(x_282)) {
case 0:
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_288 = lean_ctor_get(x_282, 0);
lean_inc(x_288);
lean_dec(x_282);
x_289 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_289, 0, x_288);
x_290 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__18;
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_289);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_287);
x_293 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13;
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_292);
x_295 = l_Lean_Json_mkObj(x_294);
x_296 = l_Lean_Json_compress(x_295);
x_297 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_298 = lean_string_append(x_297, x_296);
lean_dec(x_296);
x_299 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3;
x_300 = lean_string_append(x_298, x_299);
x_301 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_301);
return x_5;
}
case 1:
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_302 = lean_ctor_get(x_282, 0);
lean_inc(x_302);
lean_dec(x_282);
x_303 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_303, 0, x_302);
x_304 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__18;
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_303);
x_306 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_287);
x_307 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13;
x_308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_306);
x_309 = l_Lean_Json_mkObj(x_308);
x_310 = l_Lean_Json_compress(x_309);
x_311 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_312 = lean_string_append(x_311, x_310);
lean_dec(x_310);
x_313 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3;
x_314 = lean_string_append(x_312, x_313);
x_315 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_315);
return x_5;
}
default: 
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_316 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__19;
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_287);
x_318 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13;
x_319 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_317);
x_320 = l_Lean_Json_mkObj(x_319);
x_321 = l_Lean_Json_compress(x_320);
x_322 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_323 = lean_string_append(x_322, x_321);
lean_dec(x_321);
x_324 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3;
x_325 = lean_string_append(x_323, x_324);
x_326 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_326);
return x_5;
}
}
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_327 = lean_ctor_get(x_5, 1);
lean_inc(x_327);
lean_dec(x_5);
x_328 = lean_ctor_get(x_6, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_6, 1);
lean_inc(x_329);
lean_dec(x_6);
x_330 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__17;
x_331 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_329);
x_332 = lean_box(0);
x_333 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_332);
switch (lean_obj_tag(x_328)) {
case 0:
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_334 = lean_ctor_get(x_328, 0);
lean_inc(x_334);
lean_dec(x_328);
x_335 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_335, 0, x_334);
x_336 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__18;
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_335);
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_333);
x_339 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13;
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_338);
x_341 = l_Lean_Json_mkObj(x_340);
x_342 = l_Lean_Json_compress(x_341);
x_343 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_344 = lean_string_append(x_343, x_342);
lean_dec(x_342);
x_345 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3;
x_346 = lean_string_append(x_344, x_345);
x_347 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_347, 0, x_346);
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_347);
lean_ctor_set(x_348, 1, x_327);
return x_348;
}
case 1:
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_349 = lean_ctor_get(x_328, 0);
lean_inc(x_349);
lean_dec(x_328);
x_350 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_350, 0, x_349);
x_351 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__18;
x_352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_350);
x_353 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_333);
x_354 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13;
x_355 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_355, 0, x_354);
lean_ctor_set(x_355, 1, x_353);
x_356 = l_Lean_Json_mkObj(x_355);
x_357 = l_Lean_Json_compress(x_356);
x_358 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_359 = lean_string_append(x_358, x_357);
lean_dec(x_357);
x_360 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3;
x_361 = lean_string_append(x_359, x_360);
x_362 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_362, 0, x_361);
x_363 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_327);
return x_363;
}
default: 
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_364 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__19;
x_365 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_333);
x_366 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13;
x_367 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_365);
x_368 = l_Lean_Json_mkObj(x_367);
x_369 = l_Lean_Json_compress(x_368);
x_370 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_371 = lean_string_append(x_370, x_369);
lean_dec(x_369);
x_372 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3;
x_373 = lean_string_append(x_371, x_372);
x_374 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_374, 0, x_373);
x_375 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_327);
return x_375;
}
}
}
}
default: 
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; uint8_t x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
lean_dec(x_3);
x_376 = lean_ctor_get(x_5, 1);
lean_inc(x_376);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_377 = x_5;
} else {
 lean_dec_ref(x_5);
 x_377 = lean_box(0);
}
x_378 = lean_ctor_get(x_6, 0);
lean_inc(x_378);
x_379 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_380 = lean_ctor_get(x_6, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_6, 2);
lean_inc(x_381);
lean_dec(x_6);
x_382 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_382, 0, x_380);
x_383 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__20;
x_384 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_382);
x_385 = lean_box(0);
x_386 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_386, 0, x_384);
lean_ctor_set(x_386, 1, x_385);
x_387 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__21;
x_388 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_387, x_381);
lean_dec(x_381);
switch (lean_obj_tag(x_378)) {
case 0:
{
lean_object* x_424; lean_object* x_425; 
x_424 = lean_ctor_get(x_378, 0);
lean_inc(x_424);
lean_dec(x_378);
x_425 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_425, 0, x_424);
x_389 = x_425;
goto block_423;
}
case 1:
{
lean_object* x_426; lean_object* x_427; 
x_426 = lean_ctor_get(x_378, 0);
lean_inc(x_426);
lean_dec(x_378);
x_427 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_427, 0, x_426);
x_389 = x_427;
goto block_423;
}
default: 
{
lean_object* x_428; 
x_428 = lean_box(0);
x_389 = x_428;
goto block_423;
}
}
block_423:
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_390 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__18;
x_391 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_389);
switch (x_379) {
case 0:
{
lean_object* x_413; 
x_413 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__27;
x_392 = x_413;
goto block_412;
}
case 1:
{
lean_object* x_414; 
x_414 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__31;
x_392 = x_414;
goto block_412;
}
case 2:
{
lean_object* x_415; 
x_415 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__35;
x_392 = x_415;
goto block_412;
}
case 3:
{
lean_object* x_416; 
x_416 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__39;
x_392 = x_416;
goto block_412;
}
case 4:
{
lean_object* x_417; 
x_417 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__43;
x_392 = x_417;
goto block_412;
}
case 5:
{
lean_object* x_418; 
x_418 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__47;
x_392 = x_418;
goto block_412;
}
case 6:
{
lean_object* x_419; 
x_419 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__51;
x_392 = x_419;
goto block_412;
}
case 7:
{
lean_object* x_420; 
x_420 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__55;
x_392 = x_420;
goto block_412;
}
case 8:
{
lean_object* x_421; 
x_421 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__59;
x_392 = x_421;
goto block_412;
}
default: 
{
lean_object* x_422; 
x_422 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__63;
x_392 = x_422;
goto block_412;
}
}
block_412:
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_393 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__22;
x_394 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_394, 0, x_393);
lean_ctor_set(x_394, 1, x_392);
x_395 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_386);
x_396 = l_List_appendTR___rarg(x_395, x_388);
x_397 = l_Lean_Json_mkObj(x_396);
x_398 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__23;
x_399 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_399, 0, x_398);
lean_ctor_set(x_399, 1, x_397);
x_400 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_385);
x_401 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_401, 0, x_391);
lean_ctor_set(x_401, 1, x_400);
x_402 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13;
x_403 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_403, 0, x_402);
lean_ctor_set(x_403, 1, x_401);
x_404 = l_Lean_Json_mkObj(x_403);
x_405 = l_Lean_Json_compress(x_404);
x_406 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_407 = lean_string_append(x_406, x_405);
lean_dec(x_405);
x_408 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3;
x_409 = lean_string_append(x_407, x_408);
x_410 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_410, 0, x_409);
if (lean_is_scalar(x_377)) {
 x_411 = lean_alloc_ctor(1, 2, 0);
} else {
 x_411 = x_377;
 lean_ctor_set_tag(x_411, 1);
}
lean_ctor_set(x_411, 0, x_410);
lean_ctor_set(x_411, 1, x_376);
return x_411;
}
}
}
}
}
else
{
uint8_t x_429; 
lean_dec(x_3);
x_429 = !lean_is_exclusive(x_5);
if (x_429 == 0)
{
return x_5;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_430 = lean_ctor_get(x_5, 0);
x_431 = lean_ctor_get(x_5, 1);
lean_inc(x_431);
lean_inc(x_430);
lean_dec(x_5);
x_432 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_432, 0, x_430);
lean_ctor_set(x_432, 1, x_431);
return x_432;
}
}
}
}
static lean_object* _init_l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Cannot read LSP request: ");
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2(x_1, x_5, x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_io_error_to_string(x_9);
x_11 = l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__1___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_io_error_to_string(x_16);
x_19 = l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__1___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_4);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_io_error_to_string(x_26);
x_28 = l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__1___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_4, 0, x_32);
return x_4;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_4, 0);
x_34 = lean_ctor_get(x_4, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_4);
x_35 = lean_io_error_to_string(x_33);
x_36 = l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__1___closed__1;
x_37 = lean_string_append(x_36, x_35);
lean_dec(x_35);
x_38 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_34);
return x_41;
}
}
}
}
static lean_object* _init_l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Expected JSON-RPC notification, got: '");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Unexpected param '");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' for method '");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'\n");
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_readMessage(x_1, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
switch (lean_obj_tag(x_6)) {
case 0:
{
uint8_t x_7; 
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 2);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_10);
x_13 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__14;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__15;
x_18 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_17, x_11);
lean_dec(x_11);
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__18;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_16);
x_24 = l_List_appendTR___rarg(x_23, x_18);
x_25 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Json_mkObj(x_26);
x_28 = l_Lean_Json_compress(x_27);
x_29 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_33);
return x_5;
}
case 1:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_34 = lean_ctor_get(x_9, 0);
lean_inc(x_34);
lean_dec(x_9);
x_35 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__18;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_16);
x_39 = l_List_appendTR___rarg(x_38, x_18);
x_40 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_Json_mkObj(x_41);
x_43 = l_Lean_Json_compress(x_42);
x_44 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1;
x_45 = lean_string_append(x_44, x_43);
lean_dec(x_43);
x_46 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3;
x_47 = lean_string_append(x_45, x_46);
x_48 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_48);
return x_5;
}
default: 
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_49 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__19;
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_16);
x_51 = l_List_appendTR___rarg(x_50, x_18);
x_52 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13;
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Lean_Json_mkObj(x_53);
x_55 = l_Lean_Json_compress(x_54);
x_56 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1;
x_57 = lean_string_append(x_56, x_55);
lean_dec(x_55);
x_58 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3;
x_59 = lean_string_append(x_57, x_58);
x_60 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_60);
return x_5;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_61 = lean_ctor_get(x_5, 1);
lean_inc(x_61);
lean_dec(x_5);
x_62 = lean_ctor_get(x_6, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_6, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_6, 2);
lean_inc(x_64);
lean_dec(x_6);
x_65 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_65, 0, x_63);
x_66 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__14;
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__15;
x_71 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_70, x_64);
lean_dec(x_64);
switch (lean_obj_tag(x_62)) {
case 0:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_72 = lean_ctor_get(x_62, 0);
lean_inc(x_72);
lean_dec(x_62);
x_73 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__18;
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_69);
x_77 = l_List_appendTR___rarg(x_76, x_71);
x_78 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13;
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = l_Lean_Json_mkObj(x_79);
x_81 = l_Lean_Json_compress(x_80);
x_82 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1;
x_83 = lean_string_append(x_82, x_81);
lean_dec(x_81);
x_84 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3;
x_85 = lean_string_append(x_83, x_84);
x_86 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_61);
return x_87;
}
case 1:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_88 = lean_ctor_get(x_62, 0);
lean_inc(x_88);
lean_dec(x_62);
x_89 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__18;
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_69);
x_93 = l_List_appendTR___rarg(x_92, x_71);
x_94 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13;
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = l_Lean_Json_mkObj(x_95);
x_97 = l_Lean_Json_compress(x_96);
x_98 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1;
x_99 = lean_string_append(x_98, x_97);
lean_dec(x_97);
x_100 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3;
x_101 = lean_string_append(x_99, x_100);
x_102 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_61);
return x_103;
}
default: 
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_104 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__19;
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_69);
x_106 = l_List_appendTR___rarg(x_105, x_71);
x_107 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13;
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = l_Lean_Json_mkObj(x_108);
x_110 = l_Lean_Json_compress(x_109);
x_111 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1;
x_112 = lean_string_append(x_111, x_110);
lean_dec(x_110);
x_113 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3;
x_114 = lean_string_append(x_112, x_113);
x_115 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_61);
return x_116;
}
}
}
}
case 1:
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_117 = lean_ctor_get(x_5, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_118 = x_5;
} else {
 lean_dec_ref(x_5);
 x_118 = lean_box(0);
}
x_119 = lean_ctor_get(x_6, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_6, 1);
lean_inc(x_120);
lean_dec(x_6);
x_121 = lean_string_dec_eq(x_119, x_3);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_120);
x_122 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__1;
x_123 = lean_string_append(x_122, x_3);
lean_dec(x_3);
x_124 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__2;
x_125 = lean_string_append(x_123, x_124);
x_126 = lean_string_append(x_125, x_119);
lean_dec(x_119);
x_127 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3;
x_128 = lean_string_append(x_126, x_127);
x_129 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_129, 0, x_128);
if (lean_is_scalar(x_118)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_118;
 lean_ctor_set_tag(x_130, 1);
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_117);
return x_130;
}
else
{
lean_object* x_131; 
lean_dec(x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_151; 
x_151 = lean_box(0);
x_131 = x_151;
goto block_150;
}
else
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_120, 0);
lean_inc(x_152);
lean_dec(x_120);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
lean_dec(x_152);
x_154 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_154, 0, x_153);
x_131 = x_154;
goto block_150;
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_152, 0);
lean_inc(x_155);
lean_dec(x_152);
x_156 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_156, 0, x_155);
x_131 = x_156;
goto block_150;
}
}
block_150:
{
lean_object* x_132; 
x_132 = l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_fromJsonDidOpenTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_114_(x_131);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec(x_132);
x_134 = l_Lean_Json_compress(x_131);
x_135 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__2;
x_136 = lean_string_append(x_135, x_134);
lean_dec(x_134);
x_137 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__3;
x_138 = lean_string_append(x_136, x_137);
x_139 = lean_string_append(x_138, x_3);
lean_dec(x_3);
x_140 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__4;
x_141 = lean_string_append(x_139, x_140);
x_142 = lean_string_append(x_141, x_133);
lean_dec(x_133);
x_143 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_144 = lean_string_append(x_142, x_143);
x_145 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_145, 0, x_144);
if (lean_is_scalar(x_118)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_118;
 lean_ctor_set_tag(x_146, 1);
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_117);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_131);
x_147 = lean_ctor_get(x_132, 0);
lean_inc(x_147);
lean_dec(x_132);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_3);
lean_ctor_set(x_148, 1, x_147);
if (lean_is_scalar(x_118)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_118;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_117);
return x_149;
}
}
}
}
case 2:
{
uint8_t x_157; 
lean_dec(x_3);
x_157 = !lean_is_exclusive(x_5);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_158 = lean_ctor_get(x_5, 0);
lean_dec(x_158);
x_159 = lean_ctor_get(x_6, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_6, 1);
lean_inc(x_160);
lean_dec(x_6);
x_161 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__17;
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_160);
x_163 = lean_box(0);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
switch (lean_obj_tag(x_159)) {
case 0:
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_165 = lean_ctor_get(x_159, 0);
lean_inc(x_165);
lean_dec(x_159);
x_166 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_166, 0, x_165);
x_167 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__18;
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_166);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_164);
x_170 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13;
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_169);
x_172 = l_Lean_Json_mkObj(x_171);
x_173 = l_Lean_Json_compress(x_172);
x_174 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1;
x_175 = lean_string_append(x_174, x_173);
lean_dec(x_173);
x_176 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3;
x_177 = lean_string_append(x_175, x_176);
x_178 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_178);
return x_5;
}
case 1:
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_179 = lean_ctor_get(x_159, 0);
lean_inc(x_179);
lean_dec(x_159);
x_180 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_180, 0, x_179);
x_181 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__18;
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_180);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_164);
x_184 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13;
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_183);
x_186 = l_Lean_Json_mkObj(x_185);
x_187 = l_Lean_Json_compress(x_186);
x_188 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1;
x_189 = lean_string_append(x_188, x_187);
lean_dec(x_187);
x_190 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3;
x_191 = lean_string_append(x_189, x_190);
x_192 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_192);
return x_5;
}
default: 
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_193 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__19;
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_164);
x_195 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13;
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_194);
x_197 = l_Lean_Json_mkObj(x_196);
x_198 = l_Lean_Json_compress(x_197);
x_199 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1;
x_200 = lean_string_append(x_199, x_198);
lean_dec(x_198);
x_201 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3;
x_202 = lean_string_append(x_200, x_201);
x_203 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_203);
return x_5;
}
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_204 = lean_ctor_get(x_5, 1);
lean_inc(x_204);
lean_dec(x_5);
x_205 = lean_ctor_get(x_6, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_6, 1);
lean_inc(x_206);
lean_dec(x_6);
x_207 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__17;
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_206);
x_209 = lean_box(0);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
switch (lean_obj_tag(x_205)) {
case 0:
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_211 = lean_ctor_get(x_205, 0);
lean_inc(x_211);
lean_dec(x_205);
x_212 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_212, 0, x_211);
x_213 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__18;
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_212);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_210);
x_216 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13;
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_215);
x_218 = l_Lean_Json_mkObj(x_217);
x_219 = l_Lean_Json_compress(x_218);
x_220 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1;
x_221 = lean_string_append(x_220, x_219);
lean_dec(x_219);
x_222 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3;
x_223 = lean_string_append(x_221, x_222);
x_224 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_224, 0, x_223);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_204);
return x_225;
}
case 1:
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_226 = lean_ctor_get(x_205, 0);
lean_inc(x_226);
lean_dec(x_205);
x_227 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_227, 0, x_226);
x_228 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__18;
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_227);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_210);
x_231 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13;
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_230);
x_233 = l_Lean_Json_mkObj(x_232);
x_234 = l_Lean_Json_compress(x_233);
x_235 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1;
x_236 = lean_string_append(x_235, x_234);
lean_dec(x_234);
x_237 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3;
x_238 = lean_string_append(x_236, x_237);
x_239 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_239, 0, x_238);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_204);
return x_240;
}
default: 
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_241 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__19;
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_210);
x_243 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13;
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_242);
x_245 = l_Lean_Json_mkObj(x_244);
x_246 = l_Lean_Json_compress(x_245);
x_247 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1;
x_248 = lean_string_append(x_247, x_246);
lean_dec(x_246);
x_249 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3;
x_250 = lean_string_append(x_248, x_249);
x_251 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_251, 0, x_250);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_204);
return x_252;
}
}
}
}
default: 
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_3);
x_253 = lean_ctor_get(x_5, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_254 = x_5;
} else {
 lean_dec_ref(x_5);
 x_254 = lean_box(0);
}
x_255 = lean_ctor_get(x_6, 0);
lean_inc(x_255);
x_256 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_257 = lean_ctor_get(x_6, 1);
lean_inc(x_257);
x_258 = lean_ctor_get(x_6, 2);
lean_inc(x_258);
lean_dec(x_6);
x_259 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_259, 0, x_257);
x_260 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__20;
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_259);
x_262 = lean_box(0);
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
x_264 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__21;
x_265 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_264, x_258);
lean_dec(x_258);
switch (lean_obj_tag(x_255)) {
case 0:
{
lean_object* x_301; lean_object* x_302; 
x_301 = lean_ctor_get(x_255, 0);
lean_inc(x_301);
lean_dec(x_255);
x_302 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_302, 0, x_301);
x_266 = x_302;
goto block_300;
}
case 1:
{
lean_object* x_303; lean_object* x_304; 
x_303 = lean_ctor_get(x_255, 0);
lean_inc(x_303);
lean_dec(x_255);
x_304 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_304, 0, x_303);
x_266 = x_304;
goto block_300;
}
default: 
{
lean_object* x_305; 
x_305 = lean_box(0);
x_266 = x_305;
goto block_300;
}
}
block_300:
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__18;
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_266);
switch (x_256) {
case 0:
{
lean_object* x_290; 
x_290 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__27;
x_269 = x_290;
goto block_289;
}
case 1:
{
lean_object* x_291; 
x_291 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__31;
x_269 = x_291;
goto block_289;
}
case 2:
{
lean_object* x_292; 
x_292 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__35;
x_269 = x_292;
goto block_289;
}
case 3:
{
lean_object* x_293; 
x_293 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__39;
x_269 = x_293;
goto block_289;
}
case 4:
{
lean_object* x_294; 
x_294 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__43;
x_269 = x_294;
goto block_289;
}
case 5:
{
lean_object* x_295; 
x_295 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__47;
x_269 = x_295;
goto block_289;
}
case 6:
{
lean_object* x_296; 
x_296 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__51;
x_269 = x_296;
goto block_289;
}
case 7:
{
lean_object* x_297; 
x_297 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__55;
x_269 = x_297;
goto block_289;
}
case 8:
{
lean_object* x_298; 
x_298 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__59;
x_269 = x_298;
goto block_289;
}
default: 
{
lean_object* x_299; 
x_299 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__63;
x_269 = x_299;
goto block_289;
}
}
block_289:
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_270 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__22;
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_269);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_263);
x_273 = l_List_appendTR___rarg(x_272, x_265);
x_274 = l_Lean_Json_mkObj(x_273);
x_275 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__23;
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_274);
x_277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_262);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_268);
lean_ctor_set(x_278, 1, x_277);
x_279 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13;
x_280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_278);
x_281 = l_Lean_Json_mkObj(x_280);
x_282 = l_Lean_Json_compress(x_281);
x_283 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1;
x_284 = lean_string_append(x_283, x_282);
lean_dec(x_282);
x_285 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3;
x_286 = lean_string_append(x_284, x_285);
x_287 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_287, 0, x_286);
if (lean_is_scalar(x_254)) {
 x_288 = lean_alloc_ctor(1, 2, 0);
} else {
 x_288 = x_254;
 lean_ctor_set_tag(x_288, 1);
}
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_253);
return x_288;
}
}
}
}
}
else
{
uint8_t x_306; 
lean_dec(x_3);
x_306 = !lean_is_exclusive(x_5);
if (x_306 == 0)
{
return x_5;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_5, 0);
x_308 = lean_ctor_get(x_5, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_5);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
}
}
}
static lean_object* _init_l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Cannot read LSP notification: ");
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4(x_1, x_5, x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_io_error_to_string(x_9);
x_11 = l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__3___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_io_error_to_string(x_16);
x_19 = l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__3___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_4);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_io_error_to_string(x_26);
x_28 = l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__3___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_4, 0, x_32);
return x_4;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_4, 0);
x_34 = lean_ctor_get(x_4, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_4);
x_35 = lean_io_error_to_string(x_33);
x_36 = l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__3___closed__1;
x_37 = lean_string_append(x_36, x_35);
lean_dec(x_35);
x_38 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_34);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at_Lean_Server_FileWorker_initAndRunWorker___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint32_t x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_io_error_to_string(x_1);
x_4 = 10;
x_5 = lean_string_push(x_3, x_4);
x_6 = l_IO_eprint___at_IO_eprintln___spec__1(x_5, x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_initAndRunWorker___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("fwIn.txt");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_initAndRunWorker___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("fwOut.txt");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_initAndRunWorker___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("initialize");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_initAndRunWorker___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("textDocument/didOpen");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_initAndRunWorker___closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_initAndRunWorker___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_initAndRunWorker___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("] ");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_initAndRunWorker___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_initAndRunWorker___boxed__const__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initAndRunWorker(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = l_Lean_Server_FileWorker_initAndRunWorker___closed__1;
x_7 = 0;
x_8 = l_Lean_Server_maybeTee(x_6, x_7, x_1, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Server_FileWorker_initAndRunWorker___closed__2;
x_12 = 1;
x_13 = l_Lean_Server_maybeTee(x_11, x_12, x_2, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Server_FileWorker_initAndRunWorker___closed__3;
lean_inc(x_9);
x_17 = l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__1(x_9, x_16, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Server_FileWorker_initAndRunWorker___closed__4;
lean_inc(x_9);
x_20 = l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__3(x_9, x_19, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 3);
lean_inc(x_26);
lean_dec(x_22);
x_27 = l_Lean_FileMap_ofString(x_26);
lean_inc(x_24);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set(x_28, 2, x_27);
x_56 = l_Lean_Server_FileWorker_initAndRunWorker___closed__6;
x_57 = lean_string_append(x_56, x_24);
lean_dec(x_24);
x_58 = l_Lean_Server_FileWorker_initAndRunWorker___closed__7;
x_59 = lean_string_append(x_57, x_58);
x_60 = l_IO_FS_Stream_withPrefix(x_3, x_59);
lean_inc(x_60);
x_61 = lean_get_set_stderr(x_60, x_23);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
lean_inc(x_14);
lean_inc(x_28);
x_63 = l_Lean_Server_FileWorker_initializeWorker(x_28, x_9, x_14, x_60, x_4, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_st_mk_ref(x_67, x_65);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_69);
x_71 = l_Lean_Server_FileWorker_mainLoop(x_66, x_69, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_28);
lean_dec(x_14);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_st_ref_get(x_69, x_72);
lean_dec(x_69);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_73, 0);
lean_dec(x_75);
x_76 = l_Lean_Server_FileWorker_initAndRunWorker___boxed__const__2;
lean_ctor_set(x_73, 0, x_76);
return x_73;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
lean_dec(x_73);
x_78 = l_Lean_Server_FileWorker_initAndRunWorker___boxed__const__2;
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_69);
x_80 = lean_ctor_get(x_71, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_71, 1);
lean_inc(x_81);
lean_dec(x_71);
x_29 = x_80;
x_30 = x_81;
goto block_55;
}
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_63, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_63, 1);
lean_inc(x_83);
lean_dec(x_63);
x_29 = x_82;
x_30 = x_83;
goto block_55;
}
block_55:
{
lean_object* x_31; 
lean_inc(x_29);
x_31 = l_IO_eprintln___at_Lean_Server_FileWorker_initAndRunWorker___spec__5(x_29, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = lean_io_error_to_string(x_29);
x_35 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__3;
x_36 = l_Lean_Server_FileWorker_initAndRunWorker___closed__5;
x_37 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_37, 2, x_36);
lean_ctor_set(x_37, 3, x_33);
lean_ctor_set(x_37, 4, x_33);
lean_ctor_set(x_37, 5, x_34);
lean_ctor_set(x_37, 6, x_33);
lean_ctor_set(x_37, 7, x_33);
x_38 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__5;
x_39 = lean_array_push(x_38, x_37);
x_40 = l_Lean_Server_publishDiagnostics(x_28, x_39, x_14, x_32);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = l_Lean_Server_FileWorker_initAndRunWorker___boxed__const__1;
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = l_Lean_Server_FileWorker_initAndRunWorker___boxed__const__1;
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_40);
if (x_47 == 0)
{
return x_40;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_40, 0);
x_49 = lean_ctor_get(x_40, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_40);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_14);
x_51 = !lean_is_exclusive(x_31);
if (x_51 == 0)
{
return x_31;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_31, 0);
x_53 = lean_ctor_get(x_31, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_31);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
x_84 = !lean_is_exclusive(x_20);
if (x_84 == 0)
{
return x_20;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_20, 0);
x_86 = lean_ctor_get(x_20, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_20);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
x_88 = !lean_is_exclusive(x_17);
if (x_88 == 0)
{
return x_17;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_17, 0);
x_90 = lean_ctor_get(x_17, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_17);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
x_92 = !lean_is_exclusive(x_13);
if (x_92 == 0)
{
return x_13;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_13, 0);
x_94 = lean_ctor_get(x_13, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_13);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_96 = !lean_is_exclusive(x_8);
if (x_96 == 0)
{
return x_8;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_8, 0);
x_98 = lean_ctor_get(x_8, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_8);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_workerMain___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("worker initialization error: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_workerMain___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_server_worker_main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_31; lean_object* x_32; 
x_3 = lean_get_stdin(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_get_stdout(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_get_stderr(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_31 = 8;
x_32 = lean_io_get_random_bytes(x_31, x_11);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint64_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_ByteArray_toUInt64LE_x21(x_33);
x_36 = lean_unbox_uint64(x_35);
lean_dec(x_35);
x_37 = lean_uint64_to_nat(x_36);
x_38 = l_IO_setRandSeed(x_37, x_34);
lean_dec(x_37);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
lean_inc(x_10);
lean_inc(x_7);
x_40 = l_Lean_Server_FileWorker_initAndRunWorker(x_4, x_7, x_10, x_1, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_7, 1);
lean_inc(x_43);
lean_dec(x_7);
x_44 = lean_apply_1(x_43, x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get(x_10, 1);
lean_inc(x_46);
x_47 = lean_apply_1(x_46, x_45);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; uint32_t x_49; uint8_t x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_unbox_uint32(x_41);
lean_dec(x_41);
x_50 = lean_uint32_to_uint8(x_49);
x_51 = lean_io_exit(x_50, x_48);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
lean_dec(x_10);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
return x_51;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_51);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_51, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
lean_dec(x_51);
x_12 = x_56;
x_13 = x_57;
goto block_30;
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_41);
x_58 = lean_ctor_get(x_47, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_47, 1);
lean_inc(x_59);
lean_dec(x_47);
x_12 = x_58;
x_13 = x_59;
goto block_30;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_41);
x_60 = lean_ctor_get(x_44, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_44, 1);
lean_inc(x_61);
lean_dec(x_44);
x_12 = x_60;
x_13 = x_61;
goto block_30;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_7);
x_62 = lean_ctor_get(x_40, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_40, 1);
lean_inc(x_63);
lean_dec(x_40);
x_12 = x_62;
x_13 = x_63;
goto block_30;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_64 = lean_ctor_get(x_32, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_32, 1);
lean_inc(x_65);
lean_dec(x_32);
x_12 = x_64;
x_13 = x_65;
goto block_30;
}
block_30:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_io_error_to_string(x_12);
x_15 = l_Lean_Server_FileWorker_workerMain___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = l_IO_FS_Stream_putStrLn(x_10, x_18, x_13);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = l_Lean_Server_FileWorker_workerMain___boxed__const__1;
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = l_Lean_Server_FileWorker_workerMain___boxed__const__1;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Init_System_IO(lean_object*);
lean_object* initialize_Std_Data_RBMap(lean_object*);
lean_object* initialize_Lean_Environment(lean_object*);
lean_object* initialize_Lean_Data_Lsp(lean_object*);
lean_object* initialize_Lean_Data_Json_FromToJson(lean_object*);
lean_object* initialize_Lean_Util_Paths(lean_object*);
lean_object* initialize_Lean_Server_Utils(lean_object*);
lean_object* initialize_Lean_Server_Snapshots(lean_object*);
lean_object* initialize_Lean_Server_AsyncList(lean_object*);
lean_object* initialize_Lean_Server_FileWorker_Utils(lean_object*);
lean_object* initialize_Lean_Server_FileWorker_RequestHandling(lean_object*);
lean_object* initialize_Lean_Server_FileWorker_WidgetRequests(lean_object*);
lean_object* initialize_Lean_Server_Rpc_Basic(lean_object*);
lean_object* initialize_Lean_Widget_InteractiveDiagnostic(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_FileWorker(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IO(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_RBMap(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json_FromToJson(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Paths(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Utils(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Snapshots(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_AsyncList(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_FileWorker_Utils(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_FileWorker_RequestHandling(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_FileWorker_WidgetRequests(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Rpc_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Widget_InteractiveDiagnostic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_FileWorker_CancelToken_check___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___spec__1___closed__1 = _init_l_Lean_Server_FileWorker_CancelToken_check___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___spec__1___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_CancelToken_check___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___spec__1___closed__1);
l_Lean_Server_FileWorker_CancelToken_check___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___spec__1___closed__2 = _init_l_Lean_Server_FileWorker_CancelToken_check___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___spec__1___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_CancelToken_check___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___spec__1___closed__2);
l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___closed__1 = _init_l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___closed__1();
lean_mark_persistent(l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___closed__1);
l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___at_Lean_Server_FileWorker_unfoldCmdSnaps___spec__3___closed__1 = _init_l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___at_Lean_Server_FileWorker_unfoldCmdSnaps___spec__3___closed__1();
lean_mark_persistent(l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___at_Lean_Server_FileWorker_unfoldCmdSnaps___spec__3___closed__1);
l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1 = _init_l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1);
l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__2 = _init_l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__2);
l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__3 = _init_l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__3);
l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__4 = _init_l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__4);
l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__5 = _init_l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__5();
lean_mark_persistent(l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__5);
l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__1 = _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__1);
l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__2 = _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__2);
l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__3 = _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__3);
l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__4 = _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__4);
l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__5 = _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__5();
lean_mark_persistent(l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__5);
l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__6 = _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__6();
lean_mark_persistent(l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__6);
l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__7 = _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__7();
lean_mark_persistent(l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__7);
l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__8 = _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__8();
lean_mark_persistent(l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__8);
l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__9 = _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__9();
lean_mark_persistent(l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__9);
l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__10 = _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__10();
lean_mark_persistent(l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__10);
l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__1 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__1);
l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__2 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__2);
l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__3 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__3);
l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__4 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__4);
l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__5 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__5);
l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__6 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__6);
l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__7 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__7);
l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__1 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__1);
l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__1 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__1);
l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__2 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__2);
l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__3 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__3);
l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__4 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__4);
l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__5 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__5();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__5);
l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__6 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__6();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__6);
l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__7 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__7();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__7);
l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__8 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__8();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__8);
l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__9 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__9();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__9);
l_Lean_Server_FileWorker_compileHeader___closed__1 = _init_l_Lean_Server_FileWorker_compileHeader___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___closed__1);
l_Lean_Server_FileWorker_compileHeader___closed__2 = _init_l_Lean_Server_FileWorker_compileHeader___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___closed__2);
l_Lean_Server_FileWorker_compileHeader___closed__3 = _init_l_Lean_Server_FileWorker_compileHeader___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___closed__3);
l_Lean_Server_FileWorker_compileHeader___closed__4 = _init_l_Lean_Server_FileWorker_compileHeader___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___closed__4);
l_Lean_Server_FileWorker_compileHeader___closed__5 = _init_l_Lean_Server_FileWorker_compileHeader___closed__5();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___closed__5);
l_Lean_Server_FileWorker_compileHeader___closed__6 = _init_l_Lean_Server_FileWorker_compileHeader___closed__6();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___closed__6);
l_Lean_Server_FileWorker_updateDocument___lambda__3___closed__1 = _init_l_Lean_Server_FileWorker_updateDocument___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_updateDocument___lambda__3___closed__1);
l_Lean_Server_FileWorker_updateDocument___closed__1 = _init_l_Lean_Server_FileWorker_updateDocument___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_updateDocument___closed__1);
l_Lean_Server_FileWorker_handleDidChange___closed__1 = _init_l_Lean_Server_FileWorker_handleDidChange___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_handleDidChange___closed__1);
l_Lean_Server_FileWorker_handleDidChange___closed__2 = _init_l_Lean_Server_FileWorker_handleDidChange___closed__2();
l_Lean_Server_FileWorker_handleDidChange___closed__3 = _init_l_Lean_Server_FileWorker_handleDidChange___closed__3();
l_Lean_Server_FileWorker_handleDidChange___closed__4 = _init_l_Lean_Server_FileWorker_handleDidChange___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_handleDidChange___closed__4);
l_Lean_Server_FileWorker_handleDidChange___closed__5 = _init_l_Lean_Server_FileWorker_handleDidChange___closed__5();
lean_mark_persistent(l_Lean_Server_FileWorker_handleDidChange___closed__5);
l_Lean_Server_FileWorker_parseParams___rarg___closed__1 = _init_l_Lean_Server_FileWorker_parseParams___rarg___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_parseParams___rarg___closed__1);
l_Lean_Server_FileWorker_parseParams___rarg___closed__2 = _init_l_Lean_Server_FileWorker_parseParams___rarg___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_parseParams___rarg___closed__2);
l_Lean_Server_FileWorker_handleNotification___closed__1 = _init_l_Lean_Server_FileWorker_handleNotification___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_handleNotification___closed__1);
l_Lean_Server_FileWorker_handleNotification___closed__2 = _init_l_Lean_Server_FileWorker_handleNotification___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_handleNotification___closed__2);
l_Lean_Server_FileWorker_handleNotification___closed__3 = _init_l_Lean_Server_FileWorker_handleNotification___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_handleNotification___closed__3);
l_Lean_Server_FileWorker_handleNotification___closed__4 = _init_l_Lean_Server_FileWorker_handleNotification___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_handleNotification___closed__4);
l_Lean_Server_FileWorker_handleNotification___closed__5 = _init_l_Lean_Server_FileWorker_handleNotification___closed__5();
lean_mark_persistent(l_Lean_Server_FileWorker_handleNotification___closed__5);
l_Lean_Server_FileWorker_handleRequest___closed__1 = _init_l_Lean_Server_FileWorker_handleRequest___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_handleRequest___closed__1);
l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__1 = _init_l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__1();
lean_mark_persistent(l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__1);
l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__2 = _init_l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__2();
lean_mark_persistent(l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__2);
l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__3 = _init_l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__3();
lean_mark_persistent(l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__3);
l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__4 = _init_l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__4();
lean_mark_persistent(l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__4);
l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__5 = _init_l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__5();
lean_mark_persistent(l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__5);
l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__6 = _init_l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__6();
lean_mark_persistent(l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__6);
l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__7 = _init_l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__7();
lean_mark_persistent(l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__7);
l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__8 = _init_l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__8();
lean_mark_persistent(l_Std_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__8);
l_Lean_Server_FileWorker_mainLoop___closed__1 = _init_l_Lean_Server_FileWorker_mainLoop___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_mainLoop___closed__1);
l_Lean_Server_FileWorker_mainLoop___closed__2 = _init_l_Lean_Server_FileWorker_mainLoop___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_mainLoop___closed__2);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__1 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__1();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__1);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__2 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__2();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__2);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__4 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__4();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__4);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__5 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__5();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__5);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__6 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__6();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__6);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__7 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__7();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__7);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__8 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__8();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__8);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__9 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__9();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__9);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__10 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__10();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__10);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__11 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__11();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__11);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__12 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__12();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__12);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__14 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__14();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__14);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__15 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__15();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__15);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__17 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__17();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__17);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__18 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__18();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__18);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__19 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__19();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__19);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__20 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__20();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__20);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__21 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__21();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__21);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__22 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__22();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__22);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__23 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__23();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__23);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__24 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__24();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__24);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__25 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__25();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__25);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__26 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__26();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__26);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__27 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__27();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__27);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__28 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__28();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__28);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__29 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__29();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__29);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__30 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__30();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__30);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__31 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__31();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__31);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__32 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__32();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__32);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__33 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__33();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__33);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__34 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__34();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__34);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__35 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__35();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__35);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__36 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__36();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__36);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__37 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__37();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__37);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__38 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__38();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__38);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__39 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__39();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__39);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__40 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__40();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__40);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__41 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__41();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__41);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__42 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__42();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__42);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__43 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__43();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__43);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__44 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__44();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__44);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__45 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__45();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__45);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__46 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__46();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__46);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__47 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__47();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__47);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__48 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__48();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__48);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__49 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__49();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__49);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__50 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__50();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__50);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__51 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__51();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__51);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__52 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__52();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__52);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__53 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__53();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__53);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__54 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__54();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__54);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__55 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__55();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__55);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__56 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__56();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__56);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__57 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__57();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__57);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__58 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__58();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__58);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__59 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__59();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__59);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__60 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__60();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__60);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__61 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__61();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__61);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__62 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__62();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__62);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__63 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__63();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__63);
l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__1___closed__1 = _init_l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__1___closed__1();
lean_mark_persistent(l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__1___closed__1);
l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1 = _init_l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1();
lean_mark_persistent(l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1);
l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__2 = _init_l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__2();
lean_mark_persistent(l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__2);
l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__3 = _init_l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__3();
lean_mark_persistent(l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__3);
l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__4 = _init_l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__4();
lean_mark_persistent(l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__4);
l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__3___closed__1 = _init_l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__3___closed__1();
lean_mark_persistent(l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__3___closed__1);
l_Lean_Server_FileWorker_initAndRunWorker___closed__1 = _init_l_Lean_Server_FileWorker_initAndRunWorker___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_initAndRunWorker___closed__1);
l_Lean_Server_FileWorker_initAndRunWorker___closed__2 = _init_l_Lean_Server_FileWorker_initAndRunWorker___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_initAndRunWorker___closed__2);
l_Lean_Server_FileWorker_initAndRunWorker___closed__3 = _init_l_Lean_Server_FileWorker_initAndRunWorker___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_initAndRunWorker___closed__3);
l_Lean_Server_FileWorker_initAndRunWorker___closed__4 = _init_l_Lean_Server_FileWorker_initAndRunWorker___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_initAndRunWorker___closed__4);
l_Lean_Server_FileWorker_initAndRunWorker___closed__5 = _init_l_Lean_Server_FileWorker_initAndRunWorker___closed__5();
lean_mark_persistent(l_Lean_Server_FileWorker_initAndRunWorker___closed__5);
l_Lean_Server_FileWorker_initAndRunWorker___closed__6 = _init_l_Lean_Server_FileWorker_initAndRunWorker___closed__6();
lean_mark_persistent(l_Lean_Server_FileWorker_initAndRunWorker___closed__6);
l_Lean_Server_FileWorker_initAndRunWorker___closed__7 = _init_l_Lean_Server_FileWorker_initAndRunWorker___closed__7();
lean_mark_persistent(l_Lean_Server_FileWorker_initAndRunWorker___closed__7);
l_Lean_Server_FileWorker_initAndRunWorker___boxed__const__1 = _init_l_Lean_Server_FileWorker_initAndRunWorker___boxed__const__1();
lean_mark_persistent(l_Lean_Server_FileWorker_initAndRunWorker___boxed__const__1);
l_Lean_Server_FileWorker_initAndRunWorker___boxed__const__2 = _init_l_Lean_Server_FileWorker_initAndRunWorker___boxed__const__2();
lean_mark_persistent(l_Lean_Server_FileWorker_initAndRunWorker___boxed__const__2);
l_Lean_Server_FileWorker_workerMain___closed__1 = _init_l_Lean_Server_FileWorker_workerMain___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_workerMain___closed__1);
l_Lean_Server_FileWorker_workerMain___boxed__const__1 = _init_l_Lean_Server_FileWorker_workerMain___boxed__const__1();
lean_mark_persistent(l_Lean_Server_FileWorker_workerMain___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
