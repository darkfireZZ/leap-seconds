
# leap-seconds

This crate provides a means of accessing current leap second data in rust.

This is achieved through a parser that can read and provide access to the data in a
`leap-seconds.list` file. A copy of this file can be obtained from various sources. To name a
few:
 - IERS: <https://hpiers.obspm.fr/iers/bul/bulc/ntp/leap-seconds.list>
 - TZDB (from IANA): <https://data.iana.org/time-zones/tzdb/leap-seconds.list>
 - TZDB (from GitHub): <https://raw.githubusercontent.com/eggert/tz/main/leap-seconds.list>
 - Meinberg: <https://www.meinberg.de/download/ntp/leap-seconds.list>

For more information & examples have a look at the documentation:
<https://docs.rs/leap-seconds/latest/leap_seconds>

## License

This project is licensed under the [MIT License](./LICENSE-MIT) or
[version 2.0 of the Apache License](./LICENSE-APACHE).

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF
ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED
TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT
SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR
IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
DEALINGS IN THE SOFTWARE.
