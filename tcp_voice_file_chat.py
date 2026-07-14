import json
import queue
import socket
import struct
import threading
import tkinter as tk
from datetime import datetime
from pathlib import Path
from tkinter import filedialog, messagebox, ttk

import numpy as np
import pystray
import sounddevice as sd
from PIL import Image, ImageDraw

SAMPLE_RATE = 16000
CHANNELS = 1
CHANNEL_DTYPE = "int16"
BLOCKSIZE = 1024
HEADER_STRUCT = struct.Struct("!I")


class RoomChatApp:
    def __init__(self, root: tk.Tk) -> None:
        self.root = root
        self.root.title("聊天 + 文件传输")
        self.root.geometry("980x720")
        self.root.minsize(1150, 650)
        self.root.configure(bg="#f3f6fb")

        self.style = ttk.Style(self.root)
        try:
            self.style.theme_use("clam")
        except tk.TclError:
            pass
        self.style.configure("TFrame", background="#f3f6fb")
        self.style.configure("TLabel", background="#f3f6fb", foreground="#1f2937")
        self.style.configure("TLabelFrame", background="#f3f6fb", foreground="#1f2937")
        self.style.configure("TLabelframe.Label", foreground="#1f2937")
        self.style.configure("TButton", padding=(10, 6), font=("Microsoft YaHei", 10))
        self.style.configure("Accent.TButton", background="#2563eb", foreground="#ffffff")
        self.style.map("Accent.TButton", background=[("active", "#1d4ed8")])
        self.style.configure("TEntry", padding=(6, 6))

        self.sock: socket.socket | None = None
        self.server_sock: socket.socket | None = None
        self.running = True
        self.connected = False
        self.room_active = False
        self.audio_enabled = False
        self.call_state = "idle"
        self.call_popup: tk.Toplevel | None = None
        self.pending_call_from: str | None = None
        self.last_network_error = ""
        self.reconnect_attempts = 0
        self.reconnect_thread: threading.Thread | None = None
        self.reconnect_pending = False
        self.audio_queue: queue.Queue[bytes] = queue.Queue(maxsize=20)
        self.sock_lock = threading.Lock()
        self.in_stream = None
        self.out_stream = None
        self.download_dir = Path("downloads")
        self.download_dir.mkdir(exist_ok=True)
        self.chat_history_file = Path("chat_history.json")
        self.message_history: list[dict[str, str]] = []
        self.current_file_path: Path | None = None
        self.current_file_size = 0
        self.current_file_bytes = 0
        self.tray_icon: pystray.Icon | None = None
        self.should_exit = False
        self.is_room_owner = False
        self._disconnecting = False
        self._join_attempt_active = False

        self._build_ui()
        self._load_chat_history()
        self._create_tray_icon()

    def _build_ui(self) -> None:
        main = ttk.Frame(self.root, padding=16)
        main.pack(fill="both", expand=True)

        header = ttk.Frame(main)
        header.pack(fill="x", pady=(0, 10))
        ttk.Label(header, text="聊天 + 文件传输", font=("Microsoft YaHei", 16, "bold")).pack(anchor="w")
        ttk.Label(header, text="创建房间或加入房间后即可聊天、传文件、拨打实时语音。", font=("Microsoft YaHei", 10)).pack(anchor="w", pady=(4, 0))

        top = ttk.LabelFrame(main, text="连接房间", padding=10)
        top.pack(fill="x", pady=(0, 12))

        self.mode_var = tk.StringVar(value="create")
        ttk.Radiobutton(top, text="创建房间", variable=self.mode_var, value="create", command=self._toggle_mode).pack(side="left")
        ttk.Radiobutton(top, text="加入房间", variable=self.mode_var, value="join", command=self._toggle_mode).pack(side="left", padx=(10, 0))

        self.host_var = tk.StringVar(value="0.0.0.0")
        self.port_var = tk.StringVar(value="9000")
        self.room_var = tk.StringVar(value="127.0.0.1:9000")

        self.host_entry = ttk.Entry(top, textvariable=self.host_var, width=18)
        self.port_entry = ttk.Entry(top, textvariable=self.port_var, width=8)
        self.room_entry = ttk.Entry(top, textvariable=self.room_var, width=24)

        ttk.Label(top, text="监听地址").pack(side="left", padx=(15, 5))
        self.host_entry.pack(side="left")
        ttk.Label(top, text="端口").pack(side="left", padx=(8, 5))
        self.port_entry.pack(side="left")
        ttk.Label(top, text="房间地址").pack(side="left", padx=(8, 5))
        self.room_entry.pack(side="left")

        self.connect_btn = ttk.Button(top, text="创建房间", command=self.create_room, style="Accent.TButton")
        self.connect_btn.pack(side="left", padx=(12, 0))
        self.exit_btn = ttk.Button(top, text="退出房间", command=self.disconnect_room, state="disabled")
        self.exit_btn.pack(side="left", padx=(8, 0))
        self.tray_btn = ttk.Button(top, text="最小化到托盘", command=self.hide_to_tray)
        self.tray_btn.pack(side="left", padx=(8, 0))

        center = ttk.Frame(main)
        center.pack(fill="both", expand=True)

        chat_frame = ttk.Frame(center, padding=(0, 4))
        chat_frame.pack(fill="both", expand=True)
        self.chat_box = tk.Text(chat_frame, wrap="word", state="disabled", font=("Microsoft YaHei", 10), bg="#f8fafc", fg="#111827", insertbackground="#111827")
        self.chat_box.pack(side="left", fill="both", expand=True)
        sb = ttk.Scrollbar(chat_frame, orient="vertical", command=self.chat_box.yview)
        sb.pack(side="right", fill="y")
        self.chat_box.configure(yscrollcommand=sb.set)
        self.chat_box.tag_configure("system", foreground="#b45309", font=("Microsoft YaHei", 10, "bold"), spacing3=4)
        self.chat_box.tag_configure("bubble_me", background="#dcf8c6", foreground="#111827", font=("Microsoft YaHei", 10), lmargin1=140, lmargin2=12, rmargin=12, spacing3=4)
        self.chat_box.tag_configure("bubble_peer", background="#ffffff", foreground="#111827", font=("Microsoft YaHei", 10), lmargin1=12, lmargin2=140, rmargin=12, spacing3=4)
        self.chat_box.tag_configure("bubble_name", foreground="#334155", font=("Microsoft YaHei", 9, "bold"), spacing1=2, spacing3=2)
        self.chat_box.tag_configure("bubble_time", foreground="#64748b", font=("Microsoft YaHei", 8), spacing1=2, spacing3=2)

        bottom = ttk.Frame(main)
        bottom.pack(fill="x", pady=(10, 0))

        self.msg_entry = ttk.Entry(bottom)
        self.msg_entry.pack(side="left", fill="x", expand=True)
        self.msg_entry.bind("<Return>", lambda event: self.send_text_from_ui())
        self.send_btn = ttk.Button(bottom, text="发送", command=self.send_text_from_ui)
        self.send_btn.pack(side="left", padx=(8, 0))
        self.file_btn = ttk.Button(bottom, text="发送文件", command=self.send_file_from_ui)
        self.file_btn.pack(side="left", padx=(8, 0))
        self.call_btn = ttk.Button(bottom, text="拨打语音", command=self.handle_call_button)
        self.call_btn.pack(side="left", padx=(8, 0))
        self.hangup_btn = ttk.Button(bottom, text="挂断", command=self.end_call, state="disabled")
        self.hangup_btn.pack(side="left", padx=(8, 0))

        self._toggle_mode()
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)

    def _create_tray_icon(self) -> None:
        image = self._create_tray_image()
        menu = pystray.Menu(
            pystray.MenuItem("显示窗口", self.show_window, default=True),
            pystray.MenuItem("隐藏窗口", self.hide_to_tray),
            pystray.MenuItem("退出程序", self.exit_app),
        )
        self.tray_icon = pystray.Icon("room_chat", image, "房间式语音聊天", menu)
        threading.Thread(target=self.tray_icon.run, daemon=True).start()

    def _create_tray_image(self) -> Image.Image:
        image = Image.new("RGB", (64, 64), (15, 23, 42))
        drawer = ImageDraw.Draw(image)
        drawer.ellipse((8, 8, 56, 56), fill=(37, 99, 235))
        drawer.rectangle((20, 20, 44, 44), fill=(255, 255, 255))
        return image

    def show_window(self) -> None:
        self.root.deiconify()
        self.root.lift()
        self.root.attributes("-topmost", True)
        self.root.after(100, lambda: self.root.attributes("-topmost", False))

    def hide_to_tray(self) -> None:
        self.root.withdraw()
        self._append_status("已隐藏到托盘，右键托盘图标可退出程序")

    def exit_app(self) -> None:
        self.should_exit = True
        self.on_close()

    def _toggle_mode(self) -> None:
        is_create = self.mode_var.get() == "create"
        self.host_entry.configure(state="normal" if is_create else "disabled")
        self.port_entry.configure(state="normal" if is_create else "disabled")
        self.room_entry.configure(state="disabled" if is_create else "normal")
        self.connect_btn.configure(text="创建房间" if is_create else "加入房间")
        if not self.room_active:
            self.connect_btn.configure(state="normal")

    def create_room(self) -> None:
        if self.connected:
            messagebox.showinfo("提示", "已经连接，先断开后再创建或加入新的房间")
            return
        if self.mode_var.get() == "create":
            self._start_server()
        else:
            self._start_client()

    def _start_server(self) -> None:
        try:
            port = int(self.port_var.get())
        except ValueError:
            messagebox.showerror("错误", "端口必须是数字")
            return

        self._close_sockets()
        self.server_sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.server_sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.server_sock.bind((self.host_var.get(), port))
        self.server_sock.listen(1)
        self.room_active = True
        self.is_room_owner = True
        self._disconnecting = False
        self._update_room_controls(connected=False)
        self._append_status(f"房间已创建，等待连接：{self.host_var.get()}:{port}")
        for hint in self._get_join_hints(port):
            self._append_status(hint)
        threading.Thread(target=self._accept_client, daemon=True).start()

    def _accept_client(self) -> None:
        try:
            self.sock, addr = self.server_sock.accept()
        except OSError:
            return
        self.sock.settimeout(None)
        self.room_active = True
        self.is_room_owner = True
        self._disconnecting = False
        self.connected = True
        self._update_room_controls(connected=True)
        self._append_status(f"客户端已连接：{addr}")
        threading.Thread(target=self._recv_loop, daemon=True).start()

    def _start_client(self) -> None:
        value = self.room_var.get().strip()
        if ":" not in value:
            messagebox.showerror("错误", "加入房间请输入 IP:端口，例如 192.168.1.100:9000")
            return
        host, port_str = value.rsplit(":", 1)
        try:
            port = int(port_str)
        except ValueError:
            messagebox.showerror("错误", "端口必须是数字")
            return
        if host in {"0.0.0.0", "::", "::0"}:
            messagebox.showerror("连接失败", "不能把 0.0.0.0 当作客户端地址，请改成服务端的真实 IP，例如 192.168.1.10:9000，或同机测试时用 127.0.0.1:9000")
            return
        self._close_sockets()
        self._disconnecting = False
        self.reconnect_pending = False
        self.reconnect_attempts = 0
        self.room_active = True
        self._join_attempt_active = True
        self._update_room_controls(connected=False)
        try:
            self.sock = socket.create_connection((host, port), timeout=5)
            self.connected = True
            self.room_active = True
            self._update_room_controls(connected=True)
            self._append_status(f"已加入房间：{host}:{port}")
            self.sock.settimeout(None)
            self._disconnecting = False
            self._join_attempt_active = False
            threading.Thread(target=self._recv_loop, daemon=True).start()
        except ConnectionRefusedError:
            self._join_attempt_active = False
            self._append_status("连接被拒绝：服务端可能还没启动、端口不对，或者防火墙拦截了连接。")
            self._append_status("请确认：")
            self._append_status("1. 创建房间的人已经成功启动服务端")
            self._append_status("2. 输入的是服务端的真实 IP:端口，而不是 0.0.0.0")
            self._append_status("3. 端口号和创建房间时一致")
            self._append_status("4. Windows 防火墙允许此程序通过")
            self._append_status("同机测试可用：127.0.0.1:9000")
            messagebox.showerror("连接失败", "连接被拒绝。请检查服务端是否已启动、端口是否正确、以及防火墙是否允许连接。")
        except socket.timeout:
            self.last_network_error = "连接超时"
            self._join_attempt_active = False
            self._start_auto_reconnect(host, port)
        except OSError as exc:
            self.last_network_error = str(exc)
            self._join_attempt_active = False
            self._start_auto_reconnect(host, port)
        else:
            self.sock.settimeout(None)

    def _start_auto_reconnect(self, host: str, port: int) -> None:
        if self.reconnect_thread is not None and self.reconnect_thread.is_alive():
            return
        self.reconnect_attempts = 0
        self.reconnect_pending = True
        self.reconnect_thread = threading.Thread(target=self._auto_reconnect_loop, args=(host, port), daemon=True)
        self.reconnect_thread.start()

    def _auto_reconnect_loop(self, host: str, port: int) -> None:
        while self.running and self.room_active and not self.connected and self.reconnect_pending:
            self.reconnect_attempts += 1
            try:
                self.sock = socket.create_connection((host, port), timeout=3)
                self.connected = True
                self.room_active = True
                self._disconnecting = False
                self._update_room_controls(connected=True)
                self.reconnect_attempts = 0
                self.reconnect_pending = False
                threading.Thread(target=self._recv_loop, daemon=True).start()
                break
            except (OSError, socket.timeout):
                delay = min(2 + self.reconnect_attempts, 6)
                threading.Event().wait(delay)

        if self.running and self.room_active and not self.connected and self.reconnect_pending:
            pass

    def _try_reconnect_from_runtime(self) -> None:
        if self.sock is None:
            return
        try:
            self.sock.close()
        except OSError:
            pass
        self.sock = None
        self.connected = False
        self._start_auto_reconnect(self._get_last_target_host(), self._get_last_target_port())

    def _get_last_target_host(self) -> str:
        if self.room_var.get().strip() and ":" in self.room_var.get().strip():
            host, _ = self.room_var.get().strip().rsplit(":", 1)
            return host
        return "127.0.0.1"

    def _get_last_target_port(self) -> int:
        if self.room_var.get().strip() and ":" in self.room_var.get().strip():
            _, port_str = self.room_var.get().strip().rsplit(":", 1)
            try:
                return int(port_str)
            except ValueError:
                pass
        return int(self.port_var.get())

    def handle_call_button(self) -> None:
        if self.call_state == "incoming":
            self._accept_incoming_call()
            return
        self.place_call()

    def place_call(self) -> None:
        if not self.connected:
            messagebox.showwarning("提示", "先创建或加入房间")
            return
        if self.call_state in {"dialing", "in_call"}:
            return
        self.call_state = "dialing"
        self._refresh_call_ui()
        self._append_status("正在呼叫对方…")
        self.send_packet("call_invite", b"invite")

    def _accept_incoming_call(self) -> None:
        if self.call_popup is not None:
            self.call_popup.destroy()
            self.call_popup = None
        if not self.connected:
            return
        self.call_state = "in_call"
        self._refresh_call_ui()
        self._append_status("对方已接听，通话已连接")
        self.send_packet("call_accept", b"accept")
        self.start_audio()
        self.audio_enabled = True

    def _decline_incoming_call(self) -> None:
        if self.call_popup is not None:
            self.call_popup.destroy()
            self.call_popup = None
        self.call_state = "idle"
        self._refresh_call_ui()
        self._append_status("已拒绝来电")
        if self.connected:
            self.send_packet("call_decline", b"decline")

    def end_call(self) -> None:
        self.call_state = "idle"
        self._refresh_call_ui()
        self.stop_audio()
        self.audio_enabled = False
        self._append_status("通话已结束")
        if self.connected:
            self.send_packet("call_end", b"end")

    def _refresh_call_ui(self) -> None:
        if self.call_state == "incoming":
            self.call_btn.configure(text="接听", state="normal")
            self.hangup_btn.configure(text="拒绝", state="normal")
        elif self.call_state in {"dialing", "in_call"}:
            self.call_btn.configure(text="通话中", state="disabled")
            self.hangup_btn.configure(text="挂断", state="normal")
        else:
            self.call_btn.configure(text="拨打语音", state="normal" if self.connected else "disabled")
            self.hangup_btn.configure(text="挂断", state="disabled")

    def send_text_from_ui(self) -> None:
        text = self.msg_entry.get().strip()
        if not text:
            return
        self.send_text(text)
        self.msg_entry.delete(0, tk.END)

    def send_text(self, text: str) -> None:
        if self.sock is None:
            messagebox.showwarning("提示", "先创建或加入房间")
            return
        if not self.connected and self.room_active:
            self.connected = True
        if not self.connected:
            messagebox.showwarning("提示", "连接还没有准备好，请稍后再试")
            return
        self.send_packet("text", text.encode("utf-8"))
        self._append_message("我", text)

    def send_file_from_ui(self) -> None:
        if not self.connected:
            messagebox.showwarning("提示", "先创建或加入房间")
            return
        path = filedialog.askopenfilename(title="选择要发送的文件")
        if not path:
            return
        self.send_file(path)

    def send_file(self, path_str: str) -> None:
        path = Path(path_str).expanduser().resolve()
        if not path.exists() or not path.is_file():
            messagebox.showwarning("提示", "文件不存在或不是普通文件")
            return
        try:
            size = path.stat().st_size
            meta = {"name": path.name, "size": size}
            self.send_packet("file_meta", json.dumps(meta, ensure_ascii=False).encode("utf-8"))
            with path.open("rb") as f:
                while True:
                    chunk = f.read(64 * 1024)
                    if not chunk:
                        break
                    self.send_packet("file_chunk", chunk)
            self._append_status(f"文件已发送：{path}")
        except OSError as exc:
            self._append_status(f"发送文件失败：{exc}")

    def start_audio(self) -> None:
        self.in_stream = sd.InputStream(
            samplerate=SAMPLE_RATE,
            channels=CHANNELS,
            dtype=CHANNEL_DTYPE,
            blocksize=BLOCKSIZE,
            callback=self._input_callback,
        )
        self.out_stream = sd.OutputStream(
            samplerate=SAMPLE_RATE,
            channels=CHANNELS,
            dtype=CHANNEL_DTYPE,
            blocksize=BLOCKSIZE,
            callback=self._output_callback,
        )
        self.in_stream.start()
        self.out_stream.start()

    def stop_audio(self) -> None:
        if self.in_stream is not None:
            self.in_stream.stop()
            self.in_stream.close()
            self.in_stream = None
        if self.out_stream is not None:
            self.out_stream.stop()
            self.out_stream.close()
            self.out_stream = None

    def _input_callback(self, indata, frames, time_info, status) -> None:
        if status:
            self._append_status(str(status))
        if not self.audio_enabled:
            return
        payload = indata[:, 0].astype(np.int16).tobytes()
        self.send_packet("voice", payload)

    def _output_callback(self, outdata, frames, time_info, status) -> None:
        if status:
            self._append_status(str(status))
        if self.audio_queue.empty():
            outdata.fill(0)
            return
        raw = self.audio_queue.get_nowait()
        samples = np.frombuffer(raw, dtype=np.int16)
        if len(samples) < frames:
            out = np.zeros(frames, dtype=np.int16)
            out[: len(samples)] = samples
        else:
            out = samples[:frames]
        outdata[:, 0] = out.astype(np.int16)

    def _recv_loop(self) -> None:
        while self.running and self.sock is not None:
            try:
                kind, payload = self.recv_packet()
            except ConnectionResetError:
                self._handle_disconnect("对方已关闭连接")
                break
            except BrokenPipeError:
                self._handle_disconnect("连接已断开")
                break
            except socket.timeout:
                self.last_network_error = "recv_timeout"
                self._try_reconnect_from_runtime()
                break
            except OSError as exc:
                if self._disconnecting or self.sock is None:
                    break
                error_code = getattr(exc, "errno", None)
                if error_code in {10038, 10053, 10057, 9}:
                    self._handle_disconnect("对方已退出房间")
                else:
                    self._handle_disconnect(f"网络异常：{exc}")
                break

            if kind is None:
                break
            if kind == "text":
                self._append_message("对方", payload.decode("utf-8", "replace"))
            elif kind == "room_closed":
                self._handle_disconnect("房主已退出，已自动将你移出房间")
                break
            elif kind == "file_meta":
                meta = json.loads(payload.decode("utf-8"))
                self._prepare_file(meta)
                self._append_status(f"收到文件：{meta['name']} ({meta['size']} bytes)")
            elif kind == "file_chunk":
                self._write_file_chunk(payload)
            elif kind == "voice":
                self.audio_queue.put(payload)
            elif kind == "call_invite":
                self._show_incoming_call_popup()
            elif kind == "call_accept":
                self.call_state = "in_call"
                self._refresh_call_ui()
                self.audio_enabled = True
                self.start_audio()
                self._append_status("对方已接听，通话已连接")
            elif kind == "call_decline":
                self.call_state = "idle"
                self._refresh_call_ui()
                self.audio_enabled = False
                self.stop_audio()
                self._append_status("对方拒绝了通话")
            elif kind == "call_end":
                self.call_state = "idle"
                self._refresh_call_ui()
                self.audio_enabled = False
                self.stop_audio()
                self._append_status("对方已结束通话")

    def send_packet(self, kind: str, payload: bytes) -> None:
        if self.sock is None:
            return
        if not self.connected and self.room_active:
            self.connected = True
        body = kind.encode("utf-8") + b"\n" + payload
        header = HEADER_STRUCT.pack(len(body))
        with self.sock_lock:
            try:
                self.sock.sendall(header + body)
            except OSError:
                self._handle_disconnect("对方已退出房间")

    def recv_packet(self) -> tuple[str | None, bytes | None]:
        if self.sock is None:
            return None, None
        header = self._recv_exact(HEADER_STRUCT.size)
        if not header:
            return None, None
        body_len = HEADER_STRUCT.unpack(header)[0]
        body = self._recv_exact(body_len)
        if not body:
            return None, None
        kind, _, payload = body.partition(b"\n")
        return kind.decode("utf-8", "replace"), payload

    def _recv_exact(self, length: int) -> bytes:
        chunks = []
        remaining = length
        while remaining > 0:
            try:
                chunk = self.sock.recv(remaining)
            except OSError:
                return b""
            if not chunk:
                return b""
            chunks.append(chunk)
            remaining -= len(chunk)
        return b"".join(chunks)

    def _prepare_file(self, meta: dict) -> None:
        target = self.download_dir / meta["name"]
        if target.exists():
            stem = target.stem
            suffix = target.suffix
            index = 1
            while True:
                candidate = self.download_dir / f"{stem}_{index}{suffix}"
                if not candidate.exists():
                    target = candidate
                    break
                index += 1
        self.current_file_path = target
        self.current_file_size = meta["size"]
        self.current_file_bytes = 0
        target.touch(exist_ok=True)

    def _write_file_chunk(self, chunk: bytes) -> None:
        if self.current_file_path is None:
            return
        with self.current_file_path.open("ab") as f:
            f.write(chunk)
        self.current_file_bytes += len(chunk)
        if self.current_file_bytes >= self.current_file_size:
            self._append_status(f"文件接收完成：{self.current_file_path}")

    def _show_incoming_call_popup(self) -> None:
        self.root.after(0, self._do_show_incoming_call_popup)

    def _do_show_incoming_call_popup(self) -> None:
        self.call_state = "incoming"
        self._refresh_call_ui()
        if self.call_popup is not None and self.call_popup.winfo_exists():
            return
        if not self.root.winfo_viewable():
            self.show_window()
        self.call_popup = tk.Toplevel(self.root)
        self.call_popup.title("来电")
        self.call_popup.geometry("300x140")
        self.call_popup.transient(self.root)
        self.call_popup.attributes("-topmost", True)
        ttk.Label(self.call_popup, text="收到语音通话邀请", font=("Microsoft YaHei", 12, "bold")).pack(pady=(16, 6))
        ttk.Label(self.call_popup, text="对方正在呼叫你，是否接听？", font=("Microsoft YaHei", 10)).pack(pady=(0, 12))
        button_row = ttk.Frame(self.call_popup)
        button_row.pack()
        ttk.Button(button_row, text="接听", command=self._accept_incoming_call).pack(side="left", padx=(0, 8))
        ttk.Button(button_row, text="拒绝", command=self._decline_incoming_call).pack(side="left")

    def disconnect_room(self) -> None:
        if not self.room_active and self.sock is None and self.server_sock is None:
            self._append_status("当前没有正在连接的房间")
            return
        self._handle_disconnect("已退出房间", notify_peer=self.is_room_owner and self.sock is not None)

    def _handle_disconnect(self, reason: str, notify_peer: bool = False) -> None:
        if self._disconnecting and not notify_peer:
            return
        self._disconnecting = True

        def _do_reset() -> None:
            self.stop_audio()
            self.connected = False
            self.room_active = False
            self.audio_enabled = False
            self.call_state = "idle"
            self._refresh_call_ui()
            self.reconnect_pending = False
            self.reconnect_attempts = 0
            self._join_attempt_active = False
            if notify_peer and self.sock is not None:
                try:
                    self.send_packet("room_closed", b"room_closed")
                except OSError:
                    pass
            self._close_sockets()
            self._update_room_controls(connected=False)
            self.is_room_owner = False
            self._append_status(reason)
            self._disconnecting = False

        self.root.after(0, _do_reset)

    def _update_room_controls(self, connected: bool) -> None:
        self.connected = connected
        self.connect_btn.configure(state="disabled" if self.room_active else "normal")
        self.exit_btn.configure(state="normal" if self.room_active or connected else "disabled")
        state = "normal" if connected else "disabled"
        self.msg_entry.configure(state=state)
        self.send_btn.configure(state=state)
        self.file_btn.configure(state=state)
        self._refresh_call_ui()

    def _close_sockets(self) -> None:
        sock = self.sock
        server_sock = self.server_sock
        self.sock = None
        self.server_sock = None
        if sock is not None:
            try:
                sock.shutdown(socket.SHUT_RDWR)
            except OSError:
                pass
            try:
                sock.close()
            except OSError:
                pass
        if server_sock is not None:
            try:
                server_sock.close()
            except OSError:
                pass

    def _get_join_hints(self, port: int) -> list[str]:
        hints = [f"客户端加入地址示例：{self._get_local_address_hint(port)}"]
        hints.append("如果是同一台电脑测试，请使用：127.0.0.1:{port}")
        hints.append("如果是另一台电脑，请使用对方电脑的局域网 IP，例如：192.168.1.10:{port}")
        return hints

    def _get_local_address_hint(self, port: int) -> str:
        try:
            host = socket.gethostbyname(socket.gethostname())
        except OSError:
            host = "127.0.0.1"
        if host.startswith("127."):
            return f"127.0.0.1:{port}"
        return f"{host}:{port}"

    def _load_chat_history(self) -> None:
        if not self.chat_history_file.exists():
            return
        try:
            data = json.loads(self.chat_history_file.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            return
        if isinstance(data, list):
            self.message_history = [entry for entry in data if isinstance(entry, dict)]
            self._render_chat_history()

    def _save_chat_history(self) -> None:
        try:
            self.chat_history_file.write_text(json.dumps(self.message_history, ensure_ascii=False, indent=2), encoding="utf-8")
        except OSError:
            pass

    def _render_chat_history(self) -> None:
        self._clear_chat()
        for entry in self.message_history:
            self._display_chat_entry(entry["sender"], entry["text"], entry.get("timestamp", ""), entry.get("kind", "text"))

    def _append_message(self, sender: str, text: str) -> None:
        timestamp = datetime.now().strftime("%H:%M:%S")
        self.message_history.append({"sender": sender, "text": text, "timestamp": timestamp, "kind": "text"})
        self._save_chat_history()
        self._display_chat_entry(sender, text, timestamp, "text")

    def _append_status(self, text: str) -> None:
        timestamp = datetime.now().strftime("%H:%M:%S")
        self._display_chat_entry("[系统]", text, timestamp, "system")

    def _display_chat_entry(self, sender: str, text: str, timestamp: str, kind: str) -> None:
        def _do_insert() -> None:
            self.chat_box.configure(state="normal")
            if kind == "system":
                self.chat_box.insert(tk.END, f"[{timestamp}] {sender}\n", "system")
                self.chat_box.insert(tk.END, f"{text}\n\n", "system")
            else:
                tag = "bubble_me" if sender == "我" else "bubble_peer"
                self.chat_box.insert(tk.END, f"{sender}\n", ("bubble_name", tag))
                self.chat_box.insert(tk.END, f"{timestamp}\n", ("bubble_time", tag))
                self.chat_box.insert(tk.END, f"{text}\n\n", tag)
            self.chat_box.see(tk.END)
            self.chat_box.configure(state="disabled")

        self.root.after(0, _do_insert)

    def _clear_chat(self) -> None:
        def _do_clear() -> None:
            self.chat_box.configure(state="normal")
            self.chat_box.delete("1.0", tk.END)
            self.chat_box.configure(state="disabled")

        self.root.after(0, _do_clear)

    def on_close(self) -> None:
        if self.should_exit:
            self.running = False
            self.stop_audio()
            self._close_sockets()
            if self.tray_icon is not None:
                self.tray_icon.stop()
            self.root.destroy()
            return
        self.hide_to_tray()

    def stop_audio(self) -> None:
        if self.in_stream is not None:
            self.in_stream.stop()
            self.in_stream.close()
            self.in_stream = None
        if self.out_stream is not None:
            self.out_stream.stop()
            self.out_stream.close()
            self.out_stream = None


def main() -> None:
    root = tk.Tk()
    app = RoomChatApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
