<#
Создаёт ярлыки Memo Maker для текущего пользователя Windows: на рабочем столе,
в меню "Пуск" и в автозагрузке. Без ключей создаются все три.

Ярлыкам присваивается идентификатор приложения MemoMaker.App, тот же, что
выставляет себе приложение. По нему Windows показывает на панели задач иконку
Memo Maker, а не Python, и правильно закрепляет приложение на панели задач.

Запускается под тем пользователем, которому нужны ярлыки, из папки приложения:
    powershell -ExecutionPolicy Bypass -File install.ps1
    powershell -ExecutionPolicy Bypass -File install.ps1 -Autostart
#>
param(
    [string]$Python = "",
    [switch]$Desktop,
    [switch]$StartMenu,
    [switch]$Autostart
)
$ErrorActionPreference = "Stop"
if (-not ($Desktop -or $StartMenu -or $Autostart)) { $Desktop = $StartMenu = $Autostart = $true }

$app = Join-Path $PSScriptRoot "memo_maker.pyw"
$icon = Join-Path $PSScriptRoot "memo_maker.ico"
if (-not $Python) { $Python = (& py -3.12 -c "import sys; print(sys.executable)").Trim() }
$pythonw = Join-Path (Split-Path $Python) "pythonw.exe"

# иконки рисует само приложение, здесь только убеждаемся, что файлы на месте
if (-not (Test-Path $icon)) { & $Python $app --write-icons }

Add-Type -TypeDefinition @"
using System;
using System.Runtime.InteropServices;

public static class LinkAppId {
    [StructLayout(LayoutKind.Sequential, Pack = 4)]
    struct PropertyKey { public Guid fmtid; public uint pid; }

    [StructLayout(LayoutKind.Explicit, Size = 24)]
    struct PropVariant { [FieldOffset(0)] public ushort vt; [FieldOffset(8)] public IntPtr value; }

    [ComImport, Guid("886D8EEB-8CF2-4446-8D02-CDBA1DBDCF99"), InterfaceType(ComInterfaceType.InterfaceIsIUnknown)]
    interface IPropertyStore {
        [PreserveSig] int GetCount(out uint count);
        [PreserveSig] int GetAt(uint index, out PropertyKey key);
        [PreserveSig] int GetValue(ref PropertyKey key, out PropVariant value);
        [PreserveSig] int SetValue(ref PropertyKey key, ref PropVariant value);
        [PreserveSig] int Commit();
    }

    [DllImport("shell32.dll", CharSet = CharSet.Unicode, PreserveSig = false)]
    static extern void SHGetPropertyStoreFromParsingName(string path, IntPtr bindContext, int flags,
        ref Guid iid, [MarshalAs(UnmanagedType.Interface)] out IPropertyStore store);

    public static void Set(string path, string appId) {
        Guid iid = new Guid("886D8EEB-8CF2-4446-8D02-CDBA1DBDCF99");
        IPropertyStore store;
        SHGetPropertyStoreFromParsingName(path, IntPtr.Zero, 2, ref iid, out store);
        PropertyKey key = new PropertyKey { fmtid = new Guid("9F4C2855-9F79-4B39-A8D0-E1D42DE1D5F3"), pid = 5 };
        PropVariant value = new PropVariant { vt = 31, value = Marshal.StringToCoTaskMemUni(appId) };
        try {
            Marshal.ThrowExceptionForHR(store.SetValue(ref key, ref value));
            Marshal.ThrowExceptionForHR(store.Commit());
        } finally {
            Marshal.FreeCoTaskMem(value.value);
            Marshal.ReleaseComObject(store);
        }
    }
}
"@

function New-MemoMakerLink([string]$Path, [string]$Arguments) {
    $shell = New-Object -ComObject WScript.Shell
    $link = $shell.CreateShortcut($Path)
    $link.TargetPath = $pythonw
    $link.Arguments = ("`"$app`" " + $Arguments).Trim()
    $link.WorkingDirectory = $PSScriptRoot
    $link.IconLocation = "$icon,0"
    $link.Description = "Memo Maker: транскрибация встреч и мемо"
    $link.Save()
    [LinkAppId]::Set($Path, "MemoMaker.App")
    Write-Output $Path
}

if ($Desktop) { New-MemoMakerLink (Join-Path ([Environment]::GetFolderPath("Desktop")) "Memo Maker.lnk") "" }
if ($StartMenu) { New-MemoMakerLink (Join-Path ([Environment]::GetFolderPath("Programs")) "Memo Maker.lnk") "" }
if ($Autostart) { New-MemoMakerLink (Join-Path ([Environment]::GetFolderPath("Startup")) "Memo Maker.lnk") "--hidden" }
